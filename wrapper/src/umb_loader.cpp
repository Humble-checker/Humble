#include "umb_loader.hpp"
#include <archive.h>
#include <archive_entry.h>
#include <stdexcept>
#include <iostream>


using namespace std;


std::map<std::string, std::pair<void*, size_t>> UmbLoader::load(const std::string &path, const ErrorHandler* const errorHandler)
{
    errorHandler->handleInfo("Loading UMB archive: " + path);

    std::map<std::string, std::pair<void*, size_t>> files;

    archive* a = archive_read_new();
    archive_read_support_filter_all(a);
    archive_read_support_format_tar(a);

    if (archive_read_open_filename(a, path.c_str(), 10240) != ARCHIVE_OK) 
    {
        errorHandler->handleError(archive_error_string(a));
    }

    archive_entry* entry;
    while (archive_read_next_header(a, &entry) == ARCHIVE_OK) 
    {
        std::string name = archive_entry_pathname(entry);
        size_t size = static_cast<size_t>(archive_entry_size(entry));

        errorHandler->handleInfo("Loading file: " + name + " (size: " + std::to_string(size) + " bytes)");

        void* data = malloc(size);
        if (size > 0) 
        {
            archive_read_data(a, data, size);
        }

        if(!files.emplace(name, std::make_pair(data, size)).second)
        {
            errorHandler->handleError("Duplicate file " + name + " in UMB archive: " + path);
        }
    }

    errorHandler->handleInfo("Finished loading UMB archive: " + path);

    archive_read_free(a);
    return files;
}

void UmbLoader::examine(const std::string &path, const ErrorHandler *const errorHandler)
{
    std::cout << "Examining UMB archive: " << path << std::endl;

    archive* a = archive_read_new();
    archive_read_support_filter_all(a);
    archive_read_support_format_tar(a);

    if (archive_read_open_filename(a, path.c_str(), 10240) != ARCHIVE_OK) 
    {
        errorHandler->handleError(archive_error_string(a));
    }

    archive_entry* entry;
    while (archive_read_next_header(a, &entry) == ARCHIVE_OK) 
    {
        std::string name = archive_entry_pathname(entry);
        size_t size = static_cast<size_t>(archive_entry_size(entry));
        if(size > 0)
        {
            std::cout << "File: " << name << " (size: " << size << " bytes)" << std::endl;
        }
        
    }

    errorHandler->handleInfo("Finished examining UMB archive: " + path);

    archive_read_free(a);
}
