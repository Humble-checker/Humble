#pragma once

#include "error_handler.hpp"
#include <string>
#include <map>
#include <utility>

class UmbLoader
{

public:
    static std::map<std::string, std::pair<void*, size_t>> load(const std::string &path, const ErrorHandler* const errorHandler);

    static void examine(const std::string &path, const ErrorHandler* const errorHandler);

};
