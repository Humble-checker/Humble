cmake_minimum_required(VERSION 3.15)
project(Humble C CXX)

# --- Generated solver IR -----------------------------------------------------------------------
#
# The wrapper compiles the Isabelle-LLVM IR it finds in generated/. By default that is whatever is
# already there; with -DHUMBLE_BUILD_THEORIES=ON the build first re-checks the theories in thys/
# and refreshes generated/ from their export_llvm output.

set(HUMBLE_GENERATED_DIR "${CMAKE_CURRENT_SOURCE_DIR}/generated")

# Every file export_llvm writes that the wrapper consumes, relative to thys/.
set(HUMBLE_GENERATED_FILES
    fpii/modest_pmin_gs.ll
    fpii/modest_pmin_gs.h
    fpii/modest_pmax_gs.ll
    fpii/modest_pmax_gs.h
    fpii/standalone/modest_pmin_gs.ll
    fpii/standalone/modest_pmin_gs.h
    fpii/standalone/modest_pmax_gs.ll
    fpii/standalone/modest_pmax_gs.h
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
    set(ISABELLE_SESSION Maxred_LLVM CACHE STRING "Isabelle session whose theories export the solvers")
    set(ISABELLE_BUILD_OPTIONS "" CACHE STRING "Extra arguments for isabelle build, e.g. -d <dir> or -o threads=8")

    find_program(ISABELLE_EXECUTABLE isabelle HINTS ENV ISABELLE_HOME PATH_SUFFIXES bin)
    if(NOT ISABELLE_EXECUTABLE)
        message(FATAL_ERROR "isabelle not found; put it on PATH, set ISABELLE_HOME, or pass -DISABELLE_EXECUTABLE=...")
    endif()

    # bin/isabelle is a bash script. Windows cannot run it directly, so go through the Cygwin
    # bash that every Isabelle distribution for Windows ships.
    set(ISABELLE_COMMAND "${ISABELLE_EXECUTABLE}")
    if(WIN32)
        get_filename_component(isabelle_home "${ISABELLE_EXECUTABLE}" DIRECTORY)
        get_filename_component(isabelle_home "${isabelle_home}" DIRECTORY)
        find_program(ISABELLE_BASH bash HINTS "${isabelle_home}/contrib/cygwin/bin" NO_DEFAULT_PATH)
        if(NOT ISABELLE_BASH)
            message(FATAL_ERROR "Cygwin bash not found under ${isabelle_home}/contrib/cygwin; pass -DISABELLE_BASH=...")
        endif()
        set(ISABELLE_COMMAND "${ISABELLE_BASH}" "${ISABELLE_EXECUTABLE}")
    endif()

    separate_arguments(isabelle_build_options NATIVE_COMMAND "${ISABELLE_BUILD_OPTIONS}")

    file(GLOB_RECURSE theory_sources CONFIGURE_DEPENDS
        "${CMAKE_CURRENT_SOURCE_DIR}/thys/*.thy"
        "${CMAKE_CURRENT_SOURCE_DIR}/thys/ROOT"
    )

    set(copy_commands "")
    foreach(file ${HUMBLE_GENERATED_FILES})
        list(APPEND copy_commands COMMAND "${CMAKE_COMMAND}" -E copy_if_different
             "${CMAKE_CURRENT_SOURCE_DIR}/thys/${file}" "${HUMBLE_GENERATED_DIR}/")
    endforeach()

    # -c, because isabelle build otherwise skips a session its own database records as current,
    # and then does not rewrite the exports -- after a clean, they would stay missing. It rebuilds
    # only this session, not its ancestors.
    #
    # A stamp rather than the copies themselves as OUTPUT: copy_if_different leaves an unchanged
    # file's timestamp alone, so a theory edit that does not change the IR does not recompile it.
    set(stamp "${CMAKE_CURRENT_BINARY_DIR}/isabelle_theories.stamp")
    add_custom_command(
        OUTPUT "${stamp}"
        COMMAND ${ISABELLE_COMMAND} build -d . -c ${isabelle_build_options} -v "${ISABELLE_SESSION}"
        COMMAND "${CMAKE_COMMAND}" -E make_directory "${HUMBLE_GENERATED_DIR}"
        ${copy_commands}
        COMMAND "${CMAKE_COMMAND}" -E touch "${stamp}"
        WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/thys"
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
    foreach(file ${HUMBLE_GENERATED_FILES})
        get_filename_component(name "${file}" NAME)
        if(NOT EXISTS "${HUMBLE_GENERATED_DIR}/${name}")
            message(FATAL_ERROR "generated/${name} is missing; configure with -DHUMBLE_BUILD_THEORIES=ON to build it from thys/")
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
