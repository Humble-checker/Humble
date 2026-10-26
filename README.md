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
- The [AFP](https://www.isa-afp.org/) release for Isabelle2026, registered as an Isabelle component (isabelle components -u <path to AFP>/thys).
- [Isabelle-LLVM](https://github.com/lammich/isabelle_llvm), branch `2026`, in folder isabelle_llvm (git submodule update --init) or add the path to Isabelle-LLVM in your filesystem to the components (isabelle components -u <path to Isabelle LLVM>/thys)
- CMake 3.15 or later, clang, binutils, and the libarchive, nlohmann-json and Boost
  (`program_options`) development packages. On Debian/Ubuntu:
  `apt install cmake clang binutils libarchive-dev nlohmann-json3-dev libboost-program-options-dev`
- To run `humble`: a CPU with AVX-512F, or [Intel SDE](https://www.intel.com/content/www/us/en/developer/articles/tool/software-development-emulator.html)
  (`sde64 -skx -- ./build/humble ...`).

The Isabelle items are not needed when building without `-DHUMBLE_BUILD_THEORIES=ON`.

## Building (Linux only)

To build the Humble library and tool:

```bash
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DHUMBLE_BUILD_THEORIES=ON
cmake --build build -j
```

Builds the Isabelle session `Humble_LLVM` in `thys/` and copies its exported solvers to `generated/` (Humble library).
Then compiles those solvers with the C++ frontend into a single binary (Humble tool).
Leave out `-DHUMBLE_BUILD_THEORIES=ON` to build from the existing `generated/` without Isabelle.

## Building with Docker

Needs only Docker; the image installs Isabelle, the AFP and the C++ toolchain inside a container:

```bash
git submodule update --init
docker build --output type=local,dest=. .
```

This runs the build above and puts `generated/` and `build/` in the root of the repository (`.`).

## Generated results

| path | |
| --- | --- |
| `thys/fpii/modest_pmin_gs.{ll,h}`, `thys/fpii/modest_pmax_gs.{ll,h}` | solvers as exported by Isabelle |
| `thys/fpii/standalone/`, `thys/mec/standalone/`, `thys/Gabow_SCC/standalone/` | standalone exports of the individual algorithms |
| `generated/` | copies of all of the above, in the same subfolders as in `thys/` |
| `build/humble` | the model checker |

## Interactive proof mode

To check the proofs interactively in jedit (vscode is possible as well):

```bash
isabelle jedit -d . -R Maxred_LLVM
```

