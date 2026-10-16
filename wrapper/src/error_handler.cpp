#include "error_handler.hpp"
#include <stdexcept>
#include <iostream>

void BasicErrorHandler::handleInfo(const std::string& errorMessage) const
{
    if (verbose)
    {
        std::cout << "INFO: " << errorMessage << std::endl;
    }
}

void BasicErrorHandler::handleWarning(const std::string& errorMessage) const
{
    std::cout << "\033[1;33mWARNING: " << errorMessage << "\033[0m" << std::endl;
}

void BasicErrorHandler::handleError(const std::string& errorMessage) const
{
    throw std::runtime_error(errorMessage);
}

void CrashOnWarningErrorHandler::handleInfo(const std::string &errorMessage) const
{
    BasicErrorHandler::handleInfo(errorMessage);
}

void CrashOnWarningErrorHandler::handleWarning(const std::string &errorMessage) const
{
    throw std::runtime_error("WARNING as error: " + errorMessage);
}

void CrashOnWarningErrorHandler::handleError(const std::string &errorMessage) const
{
    BasicErrorHandler::handleError(errorMessage);
}
