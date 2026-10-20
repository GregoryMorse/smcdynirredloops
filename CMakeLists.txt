cmake_minimum_required(VERSION 3.20)
project(smcirred LANGUAGES C CXX)

# Portable build of the native code of the repository (plan R21a). All build products go to the build tree
# (cmake -S . -B build/cmake); nothing is written next to the sources.
#
#   cmake -S . -B build/cmake [-DSMC_BUILD_DRIVERS=ON] [-DGMP_ROOT=/path/to/gmp]
#   cmake --build build/cmake --config Release
#
# Options
#   (the x86-64 self-modifying blueprint is selected by the compiler's target architecture inside selfmodgraph.cpp: other
#   hosts build and test everything but its execution)
#   SMC_USE_VM        define USE_VM (the virtual-machine variant of the 2-SAT solver)
#   SMC_BUILD_VALIDATION  build the native 2-SAT harness of validation/native (default ON)
#   SMC_BUILD_DRIVERS build the AES / RSA / ECDSA drivers (Windows and x86 only: they use QueryPerformanceCounter and AES-NI;
#                     the generated sources are compiled as separate object libraries to bound the compiler memory)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/bin")

string(TOLOWER "${CMAKE_SYSTEM_PROCESSOR}" _smc_proc)
if(_smc_proc MATCHES "^(x86_64|amd64|x64)$" OR CMAKE_GENERATOR_PLATFORM MATCHES "^(x64)$")
  set(_smc_x86_default ON)
else()
  set(_smc_x86_default OFF)
endif()
option(SMC_USE_VM "Build the virtual-machine variant of the 2-SAT solver" OFF)
option(SMC_BUILD_VALIDATION "Build the native 2-SAT harness" ON)
option(SMC_BUILD_DRIVERS "Build the AES/RSA/ECDSA drivers" OFF)

function(smc_options target)
  if(SMC_USE_VM)
    target_compile_definitions(${target} PRIVATE USE_VM)
  endif()
  if(MSVC)
    target_compile_options(${target} PRIVATE /EHsc /W3)
  endif()
endfunction()

add_executable(selfmodgraph native/selfmodgraph.cpp native/IrredLoop.cpp)
smc_options(selfmodgraph)

if(SMC_BUILD_VALIDATION)
  add_executable(twosat_harness validation/native/twosat_harness.cpp)
  smc_options(twosat_harness)
  enable_testing()
  set(SMC_VECTORS "${CMAKE_SOURCE_DIR}/validation/data/twosat_vectors.txt")
  if(EXISTS "${SMC_VECTORS}")
    add_test(NAME twosat_vectors COMMAND twosat_harness "${SMC_VECTORS}")
  endif()
  # R19b: protected AES-128 and modular exponentiation (irreducible loops, planted 2-SAT conditions), portable C99
  add_executable(protected native/protected.c)
  add_test(NAME protected_selftest COMMAND protected)
endif()

if(SMC_BUILD_DRIVERS)
  if(NOT (WIN32 OR _smc_x86_default))
    message(FATAL_ERROR "SMC_BUILD_DRIVERS needs a Windows or x86-64 host (QueryPerformanceCounter, AES-NI)")
  endif()
  find_path(GMP_INCLUDE_DIR gmp.h HINTS "${GMP_ROOT}/include" "$ENV{GMP_ROOT}/include")
  find_library(GMP_LIBRARY NAMES gmp mpir HINTS "${GMP_ROOT}/lib" "$ENV{GMP_ROOT}/lib" PATH_SUFFIXES x64)
  # generated sources: separate object libraries (the 10.8 MB generated/aesvm.cpp needs more than 1.5 GB with MSVC)
  foreach(gen aes128vm aes192vm aes256vm aesgraph)
    add_library(gen_${gen} OBJECT generated/${gen}.c)
  endforeach()
  add_executable(aes native/aes.c native/aesmain.c
    $<TARGET_OBJECTS:gen_aes128vm> $<TARGET_OBJECTS:gen_aes192vm> $<TARGET_OBJECTS:gen_aes256vm> $<TARGET_OBJECTS:gen_aesgraph>)
  if(NOT MSVC)
    target_compile_options(aes PRIVATE -maes -msse4.1)
  endif()
  if(GMP_INCLUDE_DIR AND GMP_LIBRARY)
    foreach(gen rsa32vm rsa64vm rsa128vm rsa256vm)
      add_library(gen_${gen} OBJECT generated/${gen}.c)
    endforeach()
    add_executable(rsa native/rsa.c $<TARGET_OBJECTS:gen_rsa32vm> $<TARGET_OBJECTS:gen_rsa64vm> $<TARGET_OBJECTS:gen_rsa128vm> $<TARGET_OBJECTS:gen_rsa256vm>)
    target_include_directories(rsa PRIVATE "${GMP_INCLUDE_DIR}")
    target_link_libraries(rsa PRIVATE "${GMP_LIBRARY}")
    add_library(gen_ecdsa256vm OBJECT generated/ecdsa256vm.c)
    add_executable(ecdsa native/ecdsa.c native/dECDSA.c $<TARGET_OBJECTS:gen_ecdsa256vm>)
    target_include_directories(ecdsa PRIVATE "${GMP_INCLUDE_DIR}")
    target_link_libraries(ecdsa PRIVATE "${GMP_LIBRARY}")
  else()
    message(WARNING "GMP not found (set GMP_ROOT): rsa and ecdsa are not built")
  endif()
  add_executable(ecdsawhibox native/ecdsamain.c generated/ecdsawhibox.c)
endif()
