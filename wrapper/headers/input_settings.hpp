#pragma once
#include <string>
#include "error_handler.hpp"



class InputSettings {
public:
    InputSettings(bool crashOnWarning = false, bool verbose = false, std::string model = "", std::string avoid = "", std::string target = "")
        : crashOnWarning(crashOnWarning), verbose(verbose), model(model), avoid(avoid), target(target) {};
    ~InputSettings() = default;
    static std::pair<const InputSettings, bool> parseCommandLine(int argc, char** argv);

    const ErrorHandler* const createErrorHandler() const;

    bool isExamineUmb() const { return examineUmb; }
    bool isMaximize() const { return maximize; }

    size_t getMaxIterations() const { return maxIterations; }
    double getFpTolerance() const { return fpTolerance; }
    double getEpsilon() const { return epsilon; }

    std::string getModel() const { return model; }
    std::string getAvoid() const { return avoid; }
    std::string getTarget() const { return target; }

private:
    bool crashOnWarning;
    bool verbose;
    // Set by Boost.program_options during parsing; initialised here so that a parse that bails out
    // early (--help, a bad option) still leaves the object readable.
    bool examineUmb = false;
    bool maximize = false;

    size_t maxIterations = 100000;
    double epsilon = 1e-6;
    double fpTolerance = 1e-12;

    std::string model;
    std::string avoid;
    std::string target;

};
