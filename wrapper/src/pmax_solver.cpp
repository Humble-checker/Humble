#include "solver.hpp"

extern "C" {
#include "modest_pmax_gs.h"
}

#include <chrono>
#include <cstddef>
#include <stdexcept>
#include <string>

// See pmin_solver.cpp: assigning by name is the compile-time check on the generated layout. The
// two headers declare modest_mdp_t identically, but each translation unit may only see its own.
static modest_mdp_t toModestMdp(const StateSpace& stateSpace)
{
    static_assert(sizeof(size_t) == sizeof(modest_size_t), "index width must match modest_size_t");
    static_assert(sizeof(ProbBound) == sizeof(modest_interval_t), "ProbBound must match modest_interval_t");
    static_assert(offsetof(ProbBound, lb) == offsetof(modest_interval_t, lb), "ProbBound::lb is misplaced");
    static_assert(offsetof(ProbBound, ub) == offsetof(modest_interval_t, ub), "ProbBound::ub is misplaced");

    modest_mdp_t mdp;
    mdp.states        = reinterpret_cast<node_t*>(stateSpace.states);
    mdp.transitions   = reinterpret_cast<node_t*>(stateSpace.transitions);
    mdp.branches      = reinterpret_cast<node_t*>(stateSpace.branches);
    mdp.probabilities = reinterpret_cast<modest_interval_t*>(stateSpace.probabilities);
    mdp.avoid         = reinterpret_cast<modest_size_t*>(stateSpace.avoids);
    mdp.target        = reinterpret_cast<modest_size_t*>(stateSpace.targets);
    return mdp;
}

AnalysisResult solvePmax(const LoadedModel& model, size_t maxIterations, double epsilon, const ErrorHandler* const errorHandler)
{
    modest_mdp_t mdp = toModestMdp(model.stateSpace);

    modest_pmax_res_t result;
    const auto solverStart = std::chrono::steady_clock::now();
    compute_pmax(maxIterations, model.numStates, epsilon, &mdp, &result);
    const double solverSeconds = std::chrono::duration<double>(std::chrono::steady_clock::now() - solverStart).count();

    errorHandler->handleInfo("Analysis completed in " + std::to_string(result.iterations) + " iterations.");
    errorHandler->handleInfo("MEC quotient has " + std::to_string(result.build.mecs.mec_count)
                             + " states (input had " + std::to_string(model.numStates) + ").");

    // Unlike pmin, tool_pmax_impl solves on the MEC quotient (see its use of MEC_map_mec_map_len_ll
    // as the state count in lib/modest_pmax_gs.ll), so the bounds are indexed by quotient state.
    // mec_of is indexed by input state and holds a zero-based quotient index; mec_count is the
    // quotient's state count, and so bounds the lbs/ubs arrays.
    node_t reducedState = result.build.mecs.mec_of[model.initialState];

    if (reducedState < 0 || reducedState >= result.build.mecs.mec_count)
    {
        std::string message = "Initial state " + std::to_string(model.initialState) + " maps to MEC quotient state "
                              + std::to_string(reducedState) + ", which is outside the quotient's "
                              + std::to_string(result.build.mecs.mec_count) + " states.";
        errorHandler->handleError(message);
        throw std::runtime_error(message);
    }

    return AnalysisResult{ result.lbs[reducedState],
                           result.ubs[reducedState],
                           static_cast<size_t>(result.iterations),
                           solverSeconds };
}
