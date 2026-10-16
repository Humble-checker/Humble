#include "json_loader.hpp"

json JsonLoader::load(const std::pair<void*, size_t>& dataSizePair)
{
    return json::parse(static_cast<char*>(dataSizePair.first), static_cast<char*>(dataSizePair.first) + dataSizePair.second);
}