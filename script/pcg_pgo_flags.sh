# Compiler flags of the profile-guided GCC build; sourced by script/pcg_pgo.sh and the
# `PCG toolchain` workflow.
#
# usage: pgo_flags generate|use GCDA_DIR [EXTRA_FLAGS]
pgo_flags() {
  case $1 in
    generate)
      echo "-fprofile-generate -fprofile-update=prefer-atomic -fprofile-dir=$2 ${3:-}" ;;
    use)
      echo "-fprofile-use -fprofile-dir=$2 -fprofile-correction -fprofile-partial-training" \
        "-Wno-missing-profile -Wno-coverage-mismatch ${3:-}" ;;
    *)
      echo "pgo_flags: unknown mode $1" >&2
      return 1 ;;
  esac
}
