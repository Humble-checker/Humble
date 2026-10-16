#include "statespace_loader.hpp"
#include "umb_loader.hpp"
#include "json_loader.hpp"
#include <boost/rational.hpp>
#include <iostream>
#include <fenv.h>
#include <numeric>
#include <vector>
#include <iomanip>
#include <sstream>
#include <stdexcept>

namespace
{
    typedef std::map<std::string, std::pair<void*, size_t>> UmbEntries;

    // std::to_string gives six decimals, which cannot show the rounding-scale differences these
    // probability diagnostics are about.
    std::string exact(double value)
    {
        std::ostringstream out;
        out << std::setprecision(17) << value;
        return out.str();
    }

    size_t bitsetWords(size_t numStates)
    {
        return (numStates + 63) >> 6;
    }

    // ErrorHandler::handleError is contracted to throw; the explicit throw keeps control flow
    // provably correct for handlers that might not, since every caller here returns a value.
    [[noreturn]] void fail(const std::string& message, const ErrorHandler* const errorHandler)
    {
        errorHandler->handleError(message);
        throw std::runtime_error(message);
    }

    // std::map::operator[] default-constructs a {nullptr, 0} entry for a missing member, which the
    // solver then dereferences as a null pointer; look entries up explicitly instead.
    std::pair<void*, size_t> requireEntry(const UmbEntries& entries, const std::string& name, size_t minimumBytes, const ErrorHandler* const errorHandler)
    {
        auto entry = entries.find(name);
        if (entry == entries.end())
        {
            fail("Missing file in UMB archive: " + name, errorHandler);
        }

        if (entry->second.first == nullptr || entry->second.second < minimumBytes)
        {
            fail("File " + name + " in UMB archive holds " + std::to_string(entry->second.second)
                 + " bytes, but at least " + std::to_string(minimumBytes) + " are required.", errorHandler);
        }

        return entry->second;
    }
}

size_t* StatespaceLoader::loadStateBitset(const UmbEntries& entries, const std::string& name, size_t numStates, const ErrorHandler* const errorHandler)
{
    auto entry = requireEntry(entries, name, bitsetWords(numStates) * sizeof(size_t), errorHandler);
    return static_cast<size_t*>(entry.first);
}

size_t StatespaceLoader::loadInitialState(const UmbEntries& entries, const UmbFormat& format, size_t numStates, const ErrorHandler* const errorHandler)
{
    auto entry = entries.find(format.initialStates());
    if (entry == entries.end() || entry->second.first == nullptr || entry->second.second < bitsetWords(numStates) * sizeof(size_t))
    {
        errorHandler->handleWarning("Missing or short " + format.initialStates() + ", reporting the probability for state 0.");
        return 0;
    }

    const size_t* bits = static_cast<const size_t*>(entry->second.first);
    size_t words = bitsetWords(numStates);

    size_t initialState = numStates;
    size_t numInitialStates = 0;

    for (size_t word = 0; word < words; ++word)
    {
        for (size_t bit = bits[word]; bit != 0; bit &= bit - 1)
        {
            size_t state = (word << 6) + __builtin_ctzll(bit);
            if (state >= numStates)
            {
                continue; // padding bits beyond the last state
            }
            if (numInitialStates++ == 0)
            {
                initialState = state;
            }
        }
    }

    if (numInitialStates == 0)
    {
        errorHandler->handleWarning("No initial state marked in " + format.initialStates() + ", reporting the probability for state 0.");
        return 0;
    }

    if (numInitialStates > 1)
    {
        errorHandler->handleWarning("Model has " + std::to_string(numInitialStates)
                                    + " initial states, reporting the probability for the first one (state "
                                    + std::to_string(initialState) + ").");
    }

    errorHandler->handleInfo("Initial state: " + std::to_string(initialState));

    return initialState;
}

LoadedModel StatespaceLoader::load(const std::string& umbPath, const std::string& avoidName, const std::string& targetName, double fpTolerance, const ErrorHandler* const errorHandler)
{

    StateSpace stateSpace;

    auto entries = UmbLoader::load(umbPath, errorHandler);

    json index = JsonLoader::load(requireEntry(entries, "index.json", 1, errorHandler));

    const UmbFormat& format = UmbFormat::forIndex(index, errorHandler);

    size_t numStates = index["transition-system"]["#states"];
    size_t numTransitions = index["transition-system"]["#choices"];
    size_t numBranches = index["transition-system"]["#branches"];

    errorHandler->handleInfo("Number of states: " + std::to_string(numStates));
    errorHandler->handleInfo("Number of transitions: " + std::to_string(numTransitions));
    errorHandler->handleInfo("Number of branches: " + std::to_string(numBranches));

    if(numStates == 0)
    {
        fail("Model has no states.", errorHandler);
    }

    if(entries.find(format.stateToChoice()) == entries.end())
    {
        errorHandler->handleInfo("Missing " + format.stateToChoice() + ", assuming one choice per state.");
        if(numTransitions != numStates)
        {
            fail("Model has no " + format.stateToChoice() + " but " + std::to_string(numTransitions)
                 + " choices for " + std::to_string(numStates) + " states, so it is not a DTMC.", errorHandler);
        }
        size_t n = numStates;
        stateSpace.states = static_cast<size_t*>(malloc(sizeof(size_t) * (n + 1)));
        std::iota(stateSpace.states, stateSpace.states + n + 1, 0);
    }
    else
    {
        // Index arrays are CSR-style and carry a trailing end sentinel, hence the +1 entry.
        stateSpace.states = static_cast<size_t*>(requireEntry(entries, format.stateToChoice(), (numStates + 1) * sizeof(size_t), errorHandler).first);
    }

    
    stateSpace.transitions = static_cast<size_t*>(requireEntry(entries, format.choiceToBranch(), (numTransitions + 1) * sizeof(size_t), errorHandler).first);
    stateSpace.branches = static_cast<size_t*>(requireEntry(entries, format.branchToTarget(), numBranches * sizeof(size_t), errorHandler).first);


    std::string probabilityType = format.probabilityKind(index);
    if(probabilityType == "double")
    {
        errorHandler->handleWarning("Detected float64 (double-precision) probabilities.");
        errorHandler->handleInfo("Using floating-point probabilities. Correctness is only guaranteed if the provided probabilities are not subject to rounding errors.");
        
        stateSpace.probabilities = StatespaceLoader::loadDoubles(requireEntry(entries, format.branchProbabilities(), numBranches * sizeof(double), errorHandler), numBranches);
    }
    else if(probabilityType == "rational")
    {
        errorHandler->handleInfo("Using rational probabilities.");

        stateSpace.probabilities = StatespaceLoader::loadRationals(requireEntry(entries, format.branchProbabilities(), numBranches * sizeof(boost::rational<size_t>), errorHandler), numBranches, errorHandler);
    }
    else if(probabilityType == "double-interval")
    {
        fail("Model uses interval-valued branch probabilities (" + probabilityType + "), i.e. it is an"
             " interval MDP. Those are not supported: the solver reads a branch interval as a rounding"
             " enclosure of one exact probability, not as model uncertainty.", errorHandler);
    }
    else
    {
        fail("Unsupported branch probability type: " + probabilityType
             + ". Supported types are double and rational.", errorHandler);
    }

    StatespaceLoader::validateProbabilities(stateSpace, numTransitions, fpTolerance, errorHandler);

    if(avoidName != "")
    {
        std::string avoidFileName = format.apValues(avoidName);
        errorHandler->handleInfo("Loading avoid states from: " + avoidFileName);
        stateSpace.avoids = loadStateBitset(entries, avoidFileName, numStates, errorHandler);
    }
    else
    {
        errorHandler->handleInfo("No avoid states provided, proceeding without avoid states.");
        stateSpace.avoids = static_cast<size_t*>(calloc(bitsetWords(numStates), sizeof(size_t)));
    }

    if(targetName != "")
    {
        std::string targetFileName = format.apValues(targetName);
        errorHandler->handleInfo("Loading target states from: " + targetFileName);
        stateSpace.targets = loadStateBitset(entries, targetFileName, numStates, errorHandler);
    }
    else
    {
        errorHandler->handleWarning("No target states provided, the resulting probability will be 0.");
        errorHandler->handleInfo("No target states provided, proceeding without target states.");   
        stateSpace.targets = static_cast<size_t*>(calloc(bitsetWords(numStates), sizeof(size_t)));
    }

    return LoadedModel{ stateSpace, numStates, loadInitialState(entries, format, numStates, errorHandler) };
}


//TODO: This function can be streamlined under the assumption that we use the correct rounding modes.
boost::rational<size_t> toDoubleRangeUp(boost::rational<size_t> rat, const ErrorHandler* const errorHandler){

    // Integers in the range -2^53 + 1 to 2^53 can be exactly represented as doubles.
    // Anything larger needs to be scaled down.
    
    if(rat.numerator() >= rat.denominator() && rat.numerator() >= MAX_INT64_DOUBLE)
    {
        //Evaluate the division with rounding up the numerator, which also rounds the fraction up.
        rat.assign((rat.numerator() + rat.denominator() - 1) / rat.denominator(), 1);

        // Edge case, the numerator is too big to fit in range, workarounds are messy so we just print a warning.
        if(rat.numerator() >= MAX_INT64_DOUBLE && rat.denominator() == 1)
        {
            errorHandler->handleWarning("Numerator is more than a factor 2^53 greater than the denominator in fraction" + std::to_string(rat.numerator()) + "/" + std::to_string(rat.denominator()) + ". The result may be rounded incorrectly.");
        }
    }

    if(rat.numerator() > 0 && rat.denominator() >= rat.numerator() && rat.denominator() >= MAX_INT64_DOUBLE)
    {
        //Evaluate the division with rounding down the denominator, which rounds the fraction up.
        rat.assign(1, rat.denominator() / rat.numerator());

        //Edge case, the denominator is too big to fit in range, workarounds are messy so we just print a warning.
        if(rat.denominator() >= MAX_INT64_DOUBLE && rat.numerator() == 1)
        {
            errorHandler->handleWarning("Denominator is more than a factor 2^53 greater than the numerator in fraction" + std::to_string(rat.numerator()) + "/" + std::to_string(rat.denominator()) + ". The result may be rounded incorrectly.");
        }
    }

    return rat;
}

//TODO: This function can be streamlined under the assumption that we use the correct rounding modes.
boost::rational<size_t> toDoubleRangeDown(boost::rational<size_t> rat, const ErrorHandler* const errorHandler){

    // Integers in the range -2^53 + 1 to 2^53 can be exactly represented as doubles.
    // Anything larger needs to be scaled down.
    
    if(rat.numerator() >= rat.denominator() && rat.numerator() >= MAX_INT64_DOUBLE)
    {
        //Evaluate the division with rounding down the numerator, which also rounds the fraction down.
        rat.assign(rat.numerator() / rat.denominator(), 1);

        // Edge case, the numerator is too big to fit in range, workarounds are messy so we just print a warning.
        if(rat.numerator() >= MAX_INT64_DOUBLE && rat.denominator() == 1)
        {
            errorHandler->handleWarning("Numerator is more than a factor 2^53 greater than the denominator in fraction" + std::to_string(rat.numerator()) + "/" + std::to_string(rat.denominator()) + ". The result may be rounded incorrectly.");
        }
    }

    if(rat.numerator() > 0 && rat.denominator() >= rat.numerator() && rat.denominator() >= MAX_INT64_DOUBLE)
    {
        //Evaluate the division with rounding up the denominator, which rounds the fraction down.
        rat.assign(1, ((rat.denominator() - 1) / rat.numerator()) + 1);

        //Edge case, the denominator is too big to fit in range, workarounds are messy so we just print a warning.
        if(rat.denominator() >= MAX_INT64_DOUBLE && rat.numerator() == 1)
        {
            errorHandler->handleWarning("Denominator is more than a factor 2^53 greater than the numerator in fraction" + std::to_string(rat.numerator()) + "/" + std::to_string(rat.denominator()) + ". The result may be rounded incorrectly.");
        }
    }

    return rat;
}


ProbBound* StatespaceLoader::loadRationals(const std::pair<void*, size_t>& dataSizePair, size_t numBranches, const ErrorHandler* const errorHandler)
{
    ProbBound* probs = static_cast<ProbBound*>(malloc(sizeof(ProbBound) * numBranches));

    boost::rational<size_t>* rats = static_cast<boost::rational<size_t>*>(dataSizePair.first);

    size_t i;

    int originalRoundingMode = fegetround();

    // Both the rescaling and the division have to round in the same direction, otherwise the
    // resulting interval can exclude the true probability.
    fesetround(FE_DOWNWARD);

    for (i = 0; i < numBranches; ++i) 
    {
        boost::rational<size_t>  r = toDoubleRangeDown(rats[i], errorHandler);
        double d1 = (double)r.numerator();
        double d2 = (double)r.denominator();
        probs[i].lb = d1 / d2;
    }

    fesetround(FE_UPWARD);

    for (i = 0; i < numBranches; ++i) 
    {
        boost::rational<size_t>  r = toDoubleRangeUp(rats[i], errorHandler);
        double d1 = (double)r.numerator();
        double d2 = (double)r.denominator();
        probs[i].ub = d1 / d2;
    }

    fesetround(originalRoundingMode);

    return probs;
}

// Each choice's branch probabilities should satisfy
//
//     1 - tolerance <= sum(lb) <= 1     and     1 <= sum(ub) <= 1 + tolerance
//
// The inequalities against 1 hold for any set of intervals containing a distribution, so a model
// breaching one is wrong. Everything here is still only a warning: the tool is garbage in, garbage
// out, and a broken distribution may well be deliberate -- it is not ours to reject or repair. Use
// -c to make these fatal.
//
// The sums are accumulated with directed rounding, lower bounds downwards and upper bounds
// upwards, so each is a true bound on the exact sum and a warning only fires when the model is
// definitely at fault rather than when our own summation drifted. The cost is that a shortfall
// smaller than one representable step is invisible: rounding the sum onto the double grid either
// erases it or promotes it to a full step, so e.g. an exact sum of 1 - 2^-54 reports as 1.0.
// Round-to-nearest would be worse still -- for a choice of 1/3 + 2/3 both sums land on exactly 1.0.
void StatespaceLoader::validateProbabilities(const StateSpace& stateSpace, size_t numTransitions, double fpTolerance, const ErrorHandler* const errorHandler)
{
    // Warnings are aggregated per kind: a broken export tends to break every choice the same way,
    // and one line per choice would bury everything else.
    struct Offence
    {
        size_t count = 0;
        size_t choice = 0;
        double lower = 0.0;
        double upper = 0.0;
        double worst = 0.0;

        void note(size_t atChoice, double lowerSum, double upperSum, double severity)
        {
            if (count++ == 0 || severity > worst)
            {
                choice = atChoice;
                lower = lowerSum;
                upper = upperSum;
                worst = severity;
            }
        }
    };

    Offence emptyInterval;
    Offence lowerAboveOne;
    Offence upperBelowOne;
    Offence lowerFarBelowOne;
    Offence upperFarAboveOne;

    for (size_t choice = 0; choice < numTransitions; ++choice)
    {
        for (size_t branch = stateSpace.transitions[choice]; branch < stateSpace.transitions[choice + 1]; ++branch)
        {
            const ProbBound& probability = stateSpace.probabilities[branch];

            // Negated so that a NaN bound is caught rather than slipping through.
            if (!(probability.lb <= probability.ub))
            {
                emptyInterval.note(branch, probability.lb, probability.ub, 1.0);
            }
        }
    }

    std::vector<double> lowerSums(numTransitions, 0.0);
    std::vector<double> upperSums(numTransitions, 0.0);

    const int originalRoundingMode = fegetround();

    fesetround(FE_DOWNWARD);
    for (size_t choice = 0; choice < numTransitions; ++choice)
    {
        for (size_t branch = stateSpace.transitions[choice]; branch < stateSpace.transitions[choice + 1]; ++branch)
        {
            lowerSums[choice] += stateSpace.probabilities[branch].lb;
        }
    }

    fesetround(FE_UPWARD);
    for (size_t choice = 0; choice < numTransitions; ++choice)
    {
        for (size_t branch = stateSpace.transitions[choice]; branch < stateSpace.transitions[choice + 1]; ++branch)
        {
            upperSums[choice] += stateSpace.probabilities[branch].ub;
        }
    }

    fesetround(originalRoundingMode);

    for (size_t choice = 0; choice < numTransitions; ++choice)
    {
        const double lower = lowerSums[choice];
        const double upper = upperSums[choice];

        // Per side, report only the stronger finding: being past 1 already implies being past the
        // tolerance on that side.
        if (lower > 1.0)
        {
            lowerAboveOne.note(choice, lower, upper, lower - 1.0);
        }
        else if (lower < 1.0 - fpTolerance)
        {
            lowerFarBelowOne.note(choice, lower, upper, 1.0 - lower);
        }

        if (upper < 1.0)
        {
            upperBelowOne.note(choice, lower, upper, 1.0 - upper);
        }
        else if (upper > 1.0 + fpTolerance)
        {
            upperFarAboveOne.note(choice, lower, upper, upper - 1.0);
        }
    }

    auto report = [&](const Offence& offence, const std::string& what, bool aboutBranch)
    {
        if (offence.count == 0)
        {
            return;
        }

        const std::string subject = aboutBranch ? "branch " : "choice ";
        const std::string worstOne = offence.count > 1
            ? " (" + std::to_string(offence.count) + " in total; worst at " + subject + std::to_string(offence.choice) + ")"
            : " (at " + subject + std::to_string(offence.choice) + ")";

        errorHandler->handleWarning(what + worstOne + ": [" + exact(offence.lower) + ", " + exact(offence.upper) + "].");
    };

    report(emptyInterval, "Branch probability interval is empty or not a number", true);
    report(lowerAboveOne, "Choice probability lower bounds sum to more than 1, so no distribution fits inside the intervals", false);
    report(upperBelowOne, "Choice probability upper bounds sum to less than 1, so no distribution fits inside the intervals", false);
    report(lowerFarBelowOne, "Choice probability lower bounds sum to further below 1 than the tolerance " + exact(fpTolerance), false);
    report(upperFarAboveOne, "Choice probability upper bounds sum to further above 1 than the tolerance " + exact(fpTolerance), false);
}

ProbBound* StatespaceLoader::loadDoubles(const std::pair<void*, size_t>& dataSizePair, size_t numBranches)
{
    ProbBound* probs = static_cast<ProbBound*>(malloc(sizeof(ProbBound) * numBranches));

    double* doubles = static_cast<double*>(dataSizePair.first);

    size_t i;

    for (i = 0; i < numBranches; ++i) 
    {
        probs[i].lb = doubles[i];
        probs[i].ub = doubles[i];
    }

    return probs;
}
