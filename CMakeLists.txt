cmake_minimum_required(VERSION 3.15)
project(Humble C CXX)

include(versions.cmake)

# --- Generated solver IR -----------------------------------------------------------------------
#
# The wrapper compiles the Isabelle-LLVM IR it finds in generated/. By default that is whatever is
# already there; with -DHUMBLE_BUILD_THEORIES=ON the build first re-checks the theories in thys/
# and refreshes generated/ from their export_llvm output.

set(HUMBLE_GENERATED_DIR "${CMAKE_CURRENT_SOURCE_DIR}/generated")

# Every file export_llvm writes that is kept in generated/, relative to thys/. generated/ mirrors
# the thys/ folders, so exports with the same name in different folders do not collide.
set(HUMBLE_GENERATED_FILES
    fpii/modest_pmin_gs.ll
    fpii/modest_pmin_gs.h
    fpii/modest_pmax_gs.ll
    fpii/modest_pmax_gs.h
    fpii/standalone/modest_ii_max.ll
    fpii/standalone/modest_ii_max.h
    fpii/standalone/modest_ii_min.ll
    fpii/standalone/modest_ii_min.h
    mec/standalone/modest_mec.ll
    mec/standalone/modest_mec.h
    Gabow_SCC/standalone/modest_scc_gabow.ll
    Gabow_SCC/standalone/modest_scc_gabow.h
)

option(HUMBLE_BUILD_THEORIES "Build the Isabelle theories and regenerate generated/ from them" OFF)

if(HUMBLE_BUILD_THEORIES)
    set(ISABELLE_SESSION Humble_LLVM CACHE STRING "Isabelle session whose theories export the solvers")
    set(ISABELLE_BUILD_OPTIONS "" CACHE STRING "Extra arguments for isabelle build, e.g. -d <dir> or -o threads=8")

    # isabelle is whatever is on PATH, looked up afresh each time it runs -- nothing is cached.
    execute_process(
        COMMAND isabelle version
        RESULT_VARIABLE isabelle_result
        OUTPUT_VARIABLE isabelle_version
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    if(NOT isabelle_result EQUAL 0)
        message(FATAL_ERROR "isabelle not found on PATH (${isabelle_result})")
    endif()
    # Anchored so that 2026 accepts neither 2026-1 nor 2026-RC1.
    if(NOT isabelle_version MATCHES "^Isabelle${HUMBLE_ISABELLE_VERSION}($|[^-0-9])")
        message(FATAL_ERROR "isabelle on PATH is '${isabelle_version}', but the theories need "
                "Isabelle${HUMBLE_ISABELLE_VERSION} (see versions.cmake)")
    endif()

    separate_arguments(isabelle_build_options NATIVE_COMMAND "${ISABELLE_BUILD_OPTIONS}")

    file(GLOB_RECURSE theory_sources CONFIGURE_DEPENDS
        "${CMAKE_CURRENT_SOURCE_DIR}/thys/*.thy"
        "${CMAKE_CURRENT_SOURCE_DIR}/thys/ROOT"
        "${CMAKE_CURRENT_SOURCE_DIR}/thys/ROOTS"
        "${CMAKE_CURRENT_SOURCE_DIR}/ROOTS"
    )

    set(copy_commands "")
    foreach(file ${HUMBLE_GENERATED_FILES})
        get_filename_component(dir "${file}" DIRECTORY)
        list(APPEND copy_commands
             COMMAND "${CMAKE_COMMAND}" -E make_directory "${HUMBLE_GENERATED_DIR}/${dir}"
             COMMAND "${CMAKE_COMMAND}" -E copy_if_different
                     "${CMAKE_CURRENT_SOURCE_DIR}/thys/${file}" "${HUMBLE_GENERATED_DIR}/${dir}/")
    endforeach()

    # Run from the repository root, whose ROOTS brings in thys/ (and through it thys/lib) and the
    # Isabelle-LLVM submodule.
    #
    # -c, because isabelle build otherwise skips a session its own database records as current,
    # and then does not rewrite the exports -- after a clean, they would stay missing. It rebuilds
    # only this session, not its ancestors.
    #
    # A stamp rather than the copies themselves as OUTPUT: copy_if_different leaves an unchanged
    # file's timestamp alone, so a theory edit that does not change the IR does not recompile it.
    set(stamp "${CMAKE_CURRENT_BINARY_DIR}/isabelle_theories.stamp")
    add_custom_command(
        OUTPUT "${stamp}"
        COMMAND isabelle build -d . -c ${isabelle_build_options} -v "${ISABELLE_SESSION}"
        ${copy_commands}
        COMMAND "${CMAKE_COMMAND}" -E touch "${stamp}"
        WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
        DEPENDS ${theory_sources}
        COMMENT "Building Isabelle session ${ISABELLE_SESSION} and refreshing generated/"
        USES_TERMINAL
        VERBATIM
    )
    add_custom_target(isabelle_theories DEPENDS "${stamp}")

    # `clean` also removes what export_llvm wrote into thys/; the next build then notices they are
    # missing and makes isabelle build regenerate them. generated/ is deliberately left alone: it is
    # committed, and the default build reads it.
    list(TRANSFORM HUMBLE_GENERATED_FILES PREPEND "${CMAKE_CURRENT_SOURCE_DIR}/thys/" OUTPUT_VARIABLE thys_exports)
    set_property(TARGET isabelle_theories PROPERTY ADDITIONAL_CLEAN_FILES ${thys_exports})
else()
    # Only what the wrapper compiles; the standalone exports are not needed to build Humble.
    foreach(file fpii/modest_pmin_gs.ll fpii/modest_pmin_gs.h fpii/modest_pmax_gs.ll fpii/modest_pmax_gs.h)
        if(NOT EXISTS "${HUMBLE_GENERATED_DIR}/${file}")
            message(FATAL_ERROR "generated/${file} is missing; configure with -DHUMBLE_BUILD_THEORIES=ON to build it from thys/")
        endif()
    endforeach()
endif()

# --- Humble ------------------------------------------------------------------------------------

# Keep the binary at build/humble, where it was before the wrapper became a subdirectory.
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}")

add_subdirectory(wrapper)

if(HUMBLE_BUILD_THEORIES)
    add_dependencies(humble isabelle_theories)
endif()
