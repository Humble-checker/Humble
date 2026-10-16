#pragma once

#include "input_settings.hpp"
#include "solver.hpp"

class Analyzer {
public:
    Analyzer(const InputSettings& settings, const LoadedModel& model)
        : settings(settings), model(model) {};
    AnalysisResult analyze(const ErrorHandler* const errorHandler);
private:
    const InputSettings& settings;
    LoadedModel model;
};
