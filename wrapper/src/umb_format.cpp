#include "umb_format.hpp"

#include <stdexcept>

namespace
{
    // As emitted by PRISM 4.9 and earlier.
    class UmbFormatV0 : public UmbFormat
    {
    public:
        std::string stateToChoice() const override { return "state-to-choice.bin"; }
        std::string choiceToBranch() const override { return "choice-to-branch.bin"; }
        std::string branchToTarget() const override { return "branch-to-target.bin"; }
        std::string branchProbabilities() const override { return "branch-probabilities.bin"; }
        std::string initialStates() const override { return "initial-states.bin"; }

        std::string apValues(const std::string& atomicProposition) const override
        {
            return "annotations/aps/" + atomicProposition + "/for-states/values.bin";
        }

        // A bare string, e.g. "branch-probability-type": "double".
        std::string probabilityKind(const nlohmann::json& index) const override
        {
            return index["transition-system"]["branch-probability-type"].get<std::string>();
        }

        std::string name() const override { return "0"; }
    };

    // As emitted by PRISM 4.10. Several members were pluralised or renamed, the annotation paths
    // lost their "for-" prefix, and the probability type became an object.
    class UmbFormatV1 : public UmbFormat
    {
    public:
        std::string stateToChoice() const override { return "state-to-choices.bin"; }
        std::string choiceToBranch() const override { return "choice-to-branches.bin"; }
        std::string branchToTarget() const override { return "branch-to-target.bin"; }
        std::string branchProbabilities() const override { return "branch-to-probability.bin"; }
        std::string initialStates() const override { return "state-is-initial.bin"; }

        std::string apValues(const std::string& atomicProposition) const override
        {
            return "annotations/aps/" + atomicProposition + "/states/values.bin";
        }

        // An object, e.g. "branch-probability-type": { "type": "double", "size": 64 }.
        std::string probabilityKind(const nlohmann::json& index) const override
        {
            return index["transition-system"]["branch-probability-type"]["type"].get<std::string>();
        }

        std::string name() const override { return "1"; }
    };

    [[noreturn]] void fail(const std::string& message, const ErrorHandler* const errorHandler)
    {
        errorHandler->handleError(message);
        throw std::runtime_error(message);
    }

    // Highest revision of each major version this build was written against. A newer revision is
    // accepted with a warning, on the assumption that revisions stay backward compatible; a newer
    // major version is not.
    size_t knownRevision(size_t version)
    {
        return version == 0 ? 1 : 0;
    }
}

const UmbFormat& UmbFormat::forIndex(const nlohmann::json& index, const ErrorHandler* const errorHandler)
{
    static const UmbFormatV0 v0;
    static const UmbFormatV1 v1;

    if (!index.contains("format-version"))
    {
        fail("UMB archive has no format-version in index.json, so its layout cannot be determined.", errorHandler);
    }

    size_t version = index["format-version"].get<size_t>();
    size_t revision = index.value("format-revision", static_cast<size_t>(0));

    const UmbFormat* format = nullptr;
    switch (version)
    {
        case 0: format = &v0; break;
        case 1: format = &v1; break;
        default:
            fail("Unsupported UMB format version " + std::to_string(version) + "." + std::to_string(revision)
                 + "; this build understands versions 0 and 1.", errorHandler);
    }

    if (revision > knownRevision(version))
    {
        errorHandler->handleWarning("UMB format " + std::to_string(version) + "." + std::to_string(revision)
                                    + " is newer than this build knows (up to " + std::to_string(version) + "."
                                    + std::to_string(knownRevision(version))
                                    + "); reading it as version " + format->name() + ".");
    }

    errorHandler->handleInfo("UMB format version " + std::to_string(version) + "." + std::to_string(revision) + ".");

    return *format;
}
