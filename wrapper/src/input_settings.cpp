#include "input_settings.hpp"
#include <boost/program_options.hpp>
#include <iostream>

namespace po = boost::program_options;

std::pair<const InputSettings, bool> InputSettings::parseCommandLine(int argc, char** argv) {
    po::options_description desc("Allowed options");

    InputSettings settings;

    desc.add_options()
        ("help,h", "produce help message")
        ("cow,c", po::bool_switch(&settings.crashOnWarning)->default_value(false), "Crash on warnings")
        ("verbose,v", po::bool_switch(&settings.verbose)->default_value(false), "Enable verbose output")
        ("file", po::value<std::string>(&settings.model)->required(), "Path to the model file")
        ("avoid,a", po::value<std::string>(&settings.avoid)->default_value(""), "States to avoid")
        ("target,t", po::value<std::string>(&settings.target)->default_value(""), "Target states. If not specified, no analysis is performed (probability is 0).")
        ("max-iters", po::value<size_t>(&settings.maxIterations)->default_value(100000), "Maximum number of iterations.")
        ("eps", po::value<double>(&settings.epsilon)->default_value(1e-6), "Epsilon value for convergence.")
        ("fp-tolerance", po::value<double>(&settings.fpTolerance)->default_value(1e-12), "Slack allowed when checking that each choice's branch probabilities describe a distribution, violation causes a warning.")
        ("examine-umb,x", po::bool_switch(&settings.examineUmb)->default_value(false), "Examine UMB files.")
        ("maximize,m", po::bool_switch(&settings.maximize)->default_value(false), "Compute the maximal reachability probability (Pmax) instead of the minimal one (Pmin).");

    po::positional_options_description pos;
    pos.add("file", 1);

    po::variables_map vm;
    try {
        auto parsed = po::command_line_parser(argc, argv)
                          .options(desc)
                          .positional(pos)
                          .run();

        po::store(parsed, vm);

        if (vm.count("help")) {
            std::cout << desc << "\n";
            return std::make_pair(settings, false);
        }

        po::notify(vm);
    } catch (const po::error &e) {
        std::cerr << "Error: " << e.what() << "\n";
        std::cout << desc << "\n";
        return std::make_pair(settings, false);
    }

    return std::make_pair(settings, true);
}

const ErrorHandler* const InputSettings::createErrorHandler() const
{
    if (crashOnWarning)
    {
        return new CrashOnWarningErrorHandler(verbose);
    }
    else
    {
        return new BasicErrorHandler(verbose);
    }
}
