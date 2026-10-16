#pragma once

#include <utility>
#include <nlohmann/json.hpp>
using json = nlohmann::json;

class JsonLoader
{

public:
    static json load(const std::pair<void*, size_t>& dataSizePair);

};
