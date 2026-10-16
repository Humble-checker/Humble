#pragma once

#include <string>

class ErrorHandler
{
public:
    virtual ~ErrorHandler() = default;
    virtual void handleInfo(const std::string& errorMessage) const = 0;
    virtual void handleWarning(const std::string& errorMessage) const = 0;
    virtual void handleError(const std::string& errorMessage) const = 0;
};

class BasicErrorHandler : public ErrorHandler
{
private:
    bool verbose = false;

public:
    BasicErrorHandler(bool verbose = false) : verbose(verbose) {}
    void handleInfo(const std::string& errorMessage) const override;
    void handleWarning(const std::string& errorMessage) const override;
    void handleError(const std::string& errorMessage) const override;
};

class CrashOnWarningErrorHandler : public BasicErrorHandler
{
public:
    CrashOnWarningErrorHandler(bool verbose = false) : BasicErrorHandler(verbose) {}
    void handleInfo(const std::string& errorMessage) const override;
    void handleWarning(const std::string& errorMessage) const override; 
    void handleError(const std::string& errorMessage) const override;
};