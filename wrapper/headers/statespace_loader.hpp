#pragma once

#include "statespace.hpp"
#include "error_handler.hpp"
#include "umb_format.hpp"
#include <map>
#include <string>

#define MAX_INT64_DOUBLE 9007199254740992 //2^53
#define INT64_DOUBLE_BITS 53

// A state space plus the metadata the solvers need alongside it. The state space itself has to
// stay layout-compatible with modest_mdp_t, so it cannot carry these fields.
struct LoadedModel
{
    StateSpace stateSpace;
    size_t numStates;
    size_t initialState;
};

class StatespaceLoader
{

public:
    static LoadedModel load(const std::string& umbPath, const std::string& avoidName, const std::string& targetName, double fpTolerance, const ErrorHandler* const errorHandler);

private:
    typedef std::map<std::string, std::pair<void*, size_t>> UmbEntries;

    static ProbBound* loadRationals(const std::pair<void *, size_t> &dataSizePair, size_t numBranches, const ErrorHandler* const errorHandler);
    static ProbBound* loadDoubles(const std::pair<void *, size_t> &dataSizePair, size_t numBranches);
    static void validateProbabilities(const StateSpace& stateSpace, size_t numTransitions, double fpTolerance, const ErrorHandler* const errorHandler);
    static size_t* loadStateBitset(const UmbEntries& entries, const std::string& name, size_t numStates, const ErrorHandler* const errorHandler);
    static size_t loadInitialState(const UmbEntries& entries, const UmbFormat& format, size_t numStates, const ErrorHandler* const errorHandler);
};
