#include "solver.hpp"

extern "C" {
#include "modest_pmin_gs.h"
}

#include <chrono>
#include <cstddef>
#include <string>

// Filling modest_mdp_t field by field is what ties this file to the generated layout: if the
// struct ever gains, loses, reorders or renames a field, this stops compiling instead of quietly
// handing the solver a differently shaped record.
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

AnalysisResult solvePmin(const LoadedModel& model, size_t maxIterations, double epsilon, const ErrorHandler* const errorHandler)
{
    modest_mdp_t mdp = toModestMdp(model.stateSpace);

    modest_ii_res_t result;
    const auto solverStart = std::chrono::steady_clock::now();
    compute_II(maxIterations, model.numStates, epsilon, &mdp, &result);
    const double solverSeconds = std::chrono::duration<double>(std::chrono::steady_clock::now() - solverStart).count();

    errorHandler->handleInfo("Analysis completed in " + std::to_string(result.iterations) + " iterations.");

    // tool_pmin_impl keeps the input state indexing, so the bounds are indexed by input state.
    return AnalysisResult{ result.lbs[model.initialState],
                           result.ubs[model.initialState],
                           static_cast<size_t>(result.iterations),
                           solverSeconds };
}
