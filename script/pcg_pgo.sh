#!/usr/bin/env bash
# Profile-guided build of the stage1 compiler with GCC.
#
# usage: script/pcg_pgo.sh BUILD_DIR GCDA_DIR TRAIN_CMD [EXTRA_FLAGS]
#
# BUILD_DIR  fresh or reused CMake build directory; the profile only matches objects that are
#            compiled to the same absolute paths, so the generate and use builds share it
# GCDA_DIR   where the instrumented binary writes its profile
# TRAIN_CMD  executable that receives the path of the instrumented `lean` and runs a representative
#            workload with it
# EXTRA_FLAGS  added to the C and C++ flags of both builds, e.g. "-march=armv8.2-a"
set -euo pipefail

build=$(realpath -m "$1"); gcda=$(realpath -m "$2"); train=$3; extra=${4:-}
src=$(cd "$(dirname "$0")/.." && pwd)
jobs=$(nproc)
mkdir -p "$build" "$gcda"

configure() { # FLAGS LINKER_FLAGS
  (cd "$build" && cmake "$src" -DCMAKE_BUILD_TYPE=Release -DSTRIP_BINARIES=OFF \
    -DCMAKE_C_COMPILER=gcc -DCMAKE_CXX_COMPILER=g++ \
    -DLEAN_EXTRA_CXX_FLAGS="$1" -DLEANC_EXTRA_CC_FLAGS="$1" -DLEAN_EXTRA_LINKER_FLAGS="$2")
}

source "$src/script/pcg_pgo_flags.sh"
generate=$(pgo_flags generate "$gcda" "$extra")
use=$(pgo_flags use "$gcda" "$extra")

configure "$generate" "-fprofile-generate"
make -C "$build" -j"$jobs"

# gcov does not create directories: objects outside the CMake-managed C++ tree are written to
# GCDA_DIR/<absolute object path>.gcda
(cd "$build/stage1/lib/temp" && find . -name '*.c.o.export' -printf '%h\n' | sort -u |
  while read -r d; do mkdir -p "$gcda$build/stage1/lib/temp/${d#./}"; done)
find "$gcda" -name '*.gcda' -delete

"$train" "$build/stage1/bin/lean"

configure "$use" ""
make -C "$build" -j"$jobs"
