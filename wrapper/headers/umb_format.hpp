#pragma once

#include "error_handler.hpp"
#include <nlohmann/json.hpp>
#include <string>

// UMB is still evolving, and every archive stamps its layout in index.json as
// format-version / format-revision. Member names and some index.json encodings differ between
// versions, so the loader resolves a UmbFormat for the version it actually finds rather than
// assuming one layout. Supporting a new version means adding one subclass and one case in
// forIndex(); nothing in the loader itself hardcodes an archive member name.
class UmbFormat
{
public:
    virtual ~UmbFormat() = default;

    // Archive members describing the transition system.
    virtual std::string stateToChoice() const = 0;
    virtual std::string choiceToBranch() const = 0;
    virtual std::string branchToTarget() const = 0;
    virtual std::string branchProbabilities() const = 0;
    virtual std::string initialStates() const = 0;
    virtual std::string apValues(const std::string& atomicProposition) const = 0;

    // How this version spells the branch probability encoding in index.json.
    virtual std::string probabilityKind(const nlohmann::json& index) const = 0;

    virtual std::string name() const = 0;

    // Picks the implementation for the version stamped in index.json, or reports why it cannot.
    static const UmbFormat& forIndex(const nlohmann::json& index, const ErrorHandler* const errorHandler);
};
