cmake_minimum_required(VERSION 3.10)
project(Humble)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

include_directories(headers)

# The IR comes from generated/ in the repository root, which the top-level CMakeLists.txt can
# refresh from the theories. Configuring this directory on its own still works and reads the same.
if(NOT DEFINED HUMBLE_GENERATED_DIR)
    set(HUMBLE_GENERATED_DIR "${CMAKE_CURRENT_SOURCE_DIR}/../generated")
endif()

find_package(LibArchive REQUIRED)
find_package(nlohmann_json REQUIRED)
find_package(Boost REQUIRED COMPONENTS program_options)

# --- Isabelle-LLVM solvers -------------------------------------------------------------------
#
# Built from the generated IR in generated/ rather than linked as prebuilt .so files, so the binary is
# self-contained and the two solvers cannot interfere with each other.
#
# They define ~108 internal symbols under the same names. Linking them as shared libraries makes
# the dynamic linker silently resolve one library's internal calls to the other's copies; linking
# their objects directly fails outright on duplicate symbols. So each solver is merged with the
# support library into one relocatable object and then has every symbol except its entry point
# localised, giving each a private copy of the shared internals.

set(ISABELLE_OPT_FLAGS -O3 CACHE STRING "Optimisation flags for compiling the Isabelle-LLVM IR")

find_program(ISABELLE_CLANG NAMES clang clang-16 clang-15 clang-14)
find_program(ISABELLE_LD NAMES ld)
find_program(ISABELLE_OBJCOPY NAMES objcopy)

foreach(tool ISABELLE_CLANG ISABELLE_LD ISABELLE_OBJCOPY)
    if(NOT ${tool})
        message(FATAL_ERROR "${tool} not found; it is needed to build the Isabelle-LLVM solvers from generated/*.ll")
    endif()
endforeach()

set(ISABELLE_SUPPORT_OBJECT "${CMAKE_CURRENT_BINARY_DIR}/isabelle_support.o")
add_custom_command(
    OUTPUT "${ISABELLE_SUPPORT_OBJECT}"
    COMMAND "${ISABELLE_CLANG}" -c -fPIC ${ISABELLE_OPT_FLAGS}
            "${CMAKE_CURRENT_SOURCE_DIR}/src/lib_isabelle_llvm.c" -o "${ISABELLE_SUPPORT_OBJECT}"
    DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/src/lib_isabelle_llvm.c"
    COMMENT "Compiling Isabelle-LLVM support library"
    VERBATIM
)

set(ISABELLE_SOLVER_OBJECTS "")

# Compile one generated .ll, give it a private copy of the support library, and leave only <entry>
# visible to the rest of the link.
function(add_isabelle_solver name ir entry)
    set(raw "${CMAKE_CURRENT_BINARY_DIR}/${name}_raw.o")
    set(merged "${CMAKE_CURRENT_BINARY_DIR}/${name}_merged.o")
    set(object "${CMAKE_CURRENT_BINARY_DIR}/${name}.o")

    add_custom_command(
        OUTPUT "${object}"
        COMMAND "${ISABELLE_CLANG}" -c -fPIC ${ISABELLE_OPT_FLAGS} "${ir}" -o "${raw}"
        COMMAND "${ISABELLE_LD}" -r "${raw}" "${ISABELLE_SUPPORT_OBJECT}" -o "${merged}"
        COMMAND "${ISABELLE_OBJCOPY}" --keep-global-symbol=${entry} "${merged}" "${object}"
        # Only ${object} is a declared output; the intermediates are never read again.
        COMMAND "${CMAKE_COMMAND}" -E remove "${raw}" "${merged}"
        DEPENDS "${ir}" "${ISABELLE_SUPPORT_OBJECT}"
        COMMENT "Building Isabelle-LLVM solver ${name} (only ${entry} stays global)"
        VERBATIM
    )

    set(ISABELLE_SOLVER_OBJECTS ${ISABELLE_SOLVER_OBJECTS} "${object}" PARENT_SCOPE)
endfunction()

add_isabelle_solver(isabelle_pmin "${HUMBLE_GENERATED_DIR}/modest_pmin_gs.ll" compute_II)
add_isabelle_solver(isabelle_pmax "${HUMBLE_GENERATED_DIR}/modest_pmax_gs.ll" compute_pmax)

set_source_files_properties(${ISABELLE_SOLVER_OBJECTS} PROPERTIES EXTERNAL_OBJECT TRUE GENERATED TRUE)

# --- Executable ------------------------------------------------------------------------------

add_executable(humble
    src/main.cpp
    src/analyzer.cpp
    src/error_handler.cpp
    src/input_settings.cpp
    src/json_loader.cpp
    src/pmin_solver.cpp
    src/pmax_solver.cpp
    src/statespace_loader.cpp
    src/umb_format.cpp
    src/umb_loader.cpp
    ${ISABELLE_SOLVER_OBJECTS}
)

# generated/ is on the include path for the generated modest_*_gs.h headers, which pmin_solver.cpp and
# pmax_solver.cpp include one apiece -- they cannot both be included in a single translation unit.
target_include_directories(humble PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/headers "${HUMBLE_GENERATED_DIR}")

target_link_libraries(humble PRIVATE
    LibArchive::LibArchive
    nlohmann_json::nlohmann_json
    Boost::program_options
)
