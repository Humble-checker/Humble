#include "statespace_loader.hpp"
#include "umb_loader.hpp"
#include "input_settings.hpp"
#include "analyzer.hpp"
#include <chrono>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <stdexcept>

typedef std::chrono::steady_clock::time_point TimePoint;

static std::string secondsSince(TimePoint start) {
    std::ostringstream out;
    out << std::fixed << std::setprecision(6)
        << std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count() << " s";
    return out.str();
}

static int run(const InputSettings& settings, const ErrorHandler* const errorHandler, TimePoint started) {

    if(settings.isExamineUmb()) {
        UmbLoader::examine(settings.getModel(), errorHandler);
        return 0;
    }

    if(settings.getTarget() != "") {
        LoadedModel model = StatespaceLoader::load(settings.getModel(), settings.getAvoid(), settings.getTarget(), settings.getFpTolerance(), errorHandler);
        Analyzer analyzer(settings, model);
        AnalysisResult result = analyzer.analyze(errorHandler);

        std::cout << "Analysis finished for property: P" << (settings.isMaximize() ? "max" : "min") << "=? [ "
                    << (settings.getAvoid() != "" ? "!" + settings.getAvoid() : "true") <<  " U "
                    << settings.getTarget() <<  " ]" << std::endl;
        std::cout << "Reachability Probability: " << result.lb << " - " << result.ub << std::endl;

        // Solver time covers the Isabelle-LLVM entry point alone; total covers the whole run,
        // command line and model loading included.
        std::ostringstream solverTime;
        solverTime << std::fixed << std::setprecision(6) << result.solverSeconds << " s";
        std::cout << "Solver time: " << solverTime.str() << std::endl;
        std::cout << "Total time: " << secondsSince(started) << std::endl;
    } else {
        errorHandler->handleInfo("No target states specified, skipping analysis (reachability probability is 0).");
        return 0;
    }

    
    return 0;
}

int main(int argc, char* argv[]) {

    const TimePoint started = std::chrono::steady_clock::now();

    auto parseResult = InputSettings::parseCommandLine(argc, argv);
    if (!parseResult.second) {
        return 1;
    }
    const InputSettings& settings = parseResult.first;

    const ErrorHandler* const errorHandler = settings.createErrorHandler();

    // ErrorHandler::handleError reports by throwing, so without this every error path -- a missing
    // archive member, an unknown atomic proposition -- would terminate with a core dump.
    try {
        return run(settings, errorHandler, started);
    } catch (const std::exception& e) {
        std::cerr << "\033[1;31mERROR: " << e.what() << "\033[0m" << std::endl;
        return 1;
    }
}
