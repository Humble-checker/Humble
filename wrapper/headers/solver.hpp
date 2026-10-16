#pragma once

#include "error_handler.hpp"
#include "statespace_loader.hpp"

// Bounds on the reachability probability for the model's initial state.
struct AnalysisResult
{
    double lb;
    double ub;
    size_t iterations;
    // Wall-clock seconds spent inside the generated solver, measured around the entry point so it
    // covers the Isabelle-LLVM code and nothing else. Always measured; only reported with -s.
    double solverSeconds;
};

// Each solver lives in its own translation unit. The two Isabelle-generated headers define the same
// struct tags (modest_mdp_t, modest_interval_t, modest_size_t, ...) behind different include guards,
// so including both anywhere is a redefinition error -- neither may appear in a shared header.
AnalysisResult solvePmin(const LoadedModel& model, size_t maxIterations, double epsilon, const ErrorHandler* const errorHandler);
AnalysisResult solvePmax(const LoadedModel& model, size_t maxIterations, double epsilon, const ErrorHandler* const errorHandler);
