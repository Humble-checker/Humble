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

## Building (Linux only)

```bash
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DHUMBLE_BUILD_THEORIES=ON && cmake --build build -j
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
