# Humble

A probabilistic model checker whose solvers are formally verified in Isabelle/HOL.

## Contents

| path | |
| --- | --- |
| `thys/` | Isabelle theories of the verified solvers (see its README) |
| `wrapper/` | C++ frontend that loads UMB models and runs the solvers (see its README) |
| `generated/` | LLVM IR and C headers exported from `thys/`, which `wrapper/` compiles |
| `CMakeLists.txt` | top-level build |
| `LICENSE` | license |

NOTE: We require Isabelle/HOL version 2026, and Isabelle-LLVM version 2026.

## Prerequisites

- [Isabelle2026](https://isabelle.in.tum.de/), with `isabelle` on `PATH`.
- The [AFP](https://www.isa-afp.org/) release for Isabelle2026, registered as an Isabelle component.
- [Isabelle-LLVM](https://github.com/lammich/isabelle_llvm), branch `2026`, in folder isabelle_llvm (git submodule)
- CMake 3.15 or later, clang, binutils, and the libarchive, nlohmann-json and Boost
  (`program_options`) development packages. On Debian/Ubuntu:
  `apt install cmake clang binutils libarchive-dev nlohmann-json3-dev libboost-program-options-dev`
- To run `humble`: a CPU with AVX-512F, or [Intel SDE](https://www.intel.com/content/www/us/en/developer/articles/tool/software-development-emulator.html)
  (`sde64 -skx -- ./build/humble ...`).

The Isabelle items are not needed when building without `-DHUMBLE_BUILD_THEORIES=ON`.

## Building (Linux only)

```bash
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DHUMBLE_BUILD_THEORIES=ON
cmake --build build -j
```

Builds the Isabelle session `Maxred_LLVM` in `thys/` and copies its exported solvers to `generated/`.
Then compiles those solvers with the C++ frontend into a single binary.
Leave out `-DHUMBLE_BUILD_THEORIES=ON` to build from the existing `generated/` without Isabelle.

## Generated results

| path | |
| --- | --- |
| `thys/fpii/modest_pmin_gs.{ll,h}`, `thys/fpii/modest_pmax_gs.{ll,h}` | solvers as exported by Isabelle |
| `generated/modest_pmin_gs.{ll,h}`, `generated/modest_pmax_gs.{ll,h}` | copies of the above |
| `build/humble` | the model checker |
