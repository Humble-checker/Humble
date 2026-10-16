#include "analyzer.hpp"
#include <stdexcept>

namespace
{
    // Both solvers do their interval arithmetic with llvm.x86.avx512.vfmadd.f64 under an embedded
    // rounding mode, which assembles to vfmadd213sd {rd-sae}/{ru-sae} and has no non-AVX-512
    // encoding. Without this check the first iteration dies with an opaque SIGILL.
    void requireAvx512f(const ErrorHandler* const errorHandler)
    {
#if defined(__x86_64__) || defined(__i386__)
        if (!__builtin_cpu_supports("avx512f"))
        {
            std::string message = "The Isabelle-LLVM solvers need an AVX-512F CPU for their directed-rounding "
                                  "FMA, which this machine does not have. Run under an emulator that provides "
                                  "it, for example: sde64 -skx -- humble <args>";
            errorHandler->handleError(message);
            throw std::runtime_error(message);
        }
#endif
    }
}

AnalysisResult Analyzer::analyze(const ErrorHandler* const errorHandler)
{
    requireAvx512f(errorHandler);

    return settings.isMaximize()
        ? solvePmax(model, settings.getMaxIterations(), settings.getEpsilon(), errorHandler)
        : solvePmin(model, settings.getMaxIterations(), settings.getEpsilon(), errorHandler);
}
