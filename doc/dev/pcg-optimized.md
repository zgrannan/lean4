# The `pcg-optimized-4.36-rc1` branch

This branch is Lean v4.36.0-rc1 plus the 24 commits from `pcg-optimized` at
`57e46a766d502ca15b86ed2457d6701b33d051e2`. The import changes use 4.36's
`SearchPath.findRootWithExt`. The interpreter retains 4.36's frame sizing,
return-type handling, and diagnostics for unreachable IR bodies.

The workflow runs the `elab`, `elab_fail`, `compile`, and `docparse` test piles before publishing
an ordinary toolchain. The PGO profiles remain those recorded for the 4.35-based toolchain;
GCC ignores profiles that do not match a function's current source.

## Changes

| Commit | Effect |
| --- | --- |
| `IO.appPath` uses the `readlink` length | The result was not NUL-terminated; under valgrind it contained stale bytes and broke every file that compiles a definition. |
| Import resolves the search path entry once per root package | Importing probed every search path entry for every module (about 40k failing `stat` calls per process, which also serialize on directory locks when many `lean` processes run). |
| `lean_mark_persistent` / `lean_mark_mt` skip scalars and persistent objects before the worklist | Fewer worklist operations during import. |
| Compiled form for persistent IR declarations in the interpreter | Imported IR is decoded once per thread; callees and partial applications are resolved once. The values of constants stay per interpreter, because a constant can be a closure over the interpreter's environment. `LEAN_IR_NO_COMPILE=1` disables it, `LEAN_IR_COMPILE_THRESHOLD=n` compiles on the n-th call. |
| `FixedParams` finds the mutual block of a call by hash | The analysis scanned every declaration of the block for every application. |
| `replace_rec_fn` takes the callback as a template parameter and uses an open-addressing cache | `instantiate`, `abstract`, ... no longer go through `std::function` and `std::unordered_map`. |
| `lean.skipIlean` (opt-in) | Writes `.ilean` files without references and declarations. |

## Measurements of the 4.35.0 toolchain

The 4.35.0 version produced the same `.olean`, `.ilean`, `.c`, and message output as upstream
v4.35.0, apart from the githash in the `.olean` header, across 1306 modules. It passed 3816 tests
in the `elab`, `elab_fail`, `compile`, and `docparse` piles. The measurements that follow are for
that version.

Callgrind instruction counts (`valgrind --tool=callgrind`, one `lean` invocation per module as Lake
runs it, imports and options from the module's `.setup.json`):

| Module | v4.35.0 (gcc build) | `pcg-optimized` + PGO (local build) |
| --- | --- | --- |
| `MIR.SwitchInt` (import dominated) | 1.760 G | 1.299 G (−26%) |
| `Core.Doc.Interp.Resolve` | 9.555 G | 8.470 G (−11%) |
| `Properties.RuntimeBorrowCompleteness.Provenance.Internal` (tactics) | 11.149 G | 9.699 G (−13%) |
| `PCG.Owned.OwnedState` (interpreter heavy) | 23.096 G | 14.012 G (−39%) |
| `Core.Dsl.DefCoe` (code generation heavy) | 30.663 G | 23.282 G (−24%) |

The official toolchain (clang) executes about 4% fewer instructions than the unmodified gcc build.

Clean `lake build Runtime Core Export MIR PCG OpSem Properties Presentation Frame SubView Spec`
(1447 jobs, 32 cores, dependencies prebuilt): official toolchain 253 s, 291 s, 305 s; this
toolchain 183 s, 170 s, 166 s.

The toolchain that the workflow builds (GCC 13, aarch64) executes 4-6% fewer instructions with the
profile than without it, and uses 8-10% less user CPU time (minimum of five runs):
`PCG.Owned.OwnedState` 2.14 s to 1.93 s, `Core.Dsl.DefCoe` 3.22 s to 2.95 s,
`Core.Doc.Interp.Resolve` 1.33 s to 1.20 s. The local PGO build above (GCC 15) saves 13-17%.

## Builds

The `PCG toolchain` workflow (`.github/workflows/pcg-toolchain.yml`) builds the toolchain with GCC for
aarch64 (`-march=armv8.2-a`) and x86_64 Linux on every push to this branch and publishes it as the
artifact `pcg-lean-linux_<arch>`. It builds with `LEAN_STANDALONE=ON` and the linker flags of the official
Linux builds, and bundles the static libraries (`libgmp.a`, `libssl.a`, `libcrypto.a`, `libuv.a`) in
`lib/lean`, so that `leanc` links executables on machines without development packages; a smoke test
links and runs an executable.

The compiler is built with profile-guided optimization (`-fprofile-use`) from
`script/pgo/profile-<arch>.tar.xz`. The profile names every object file by its absolute path, which
is why the instrumented and the final build both run in `$GITHUB_WORKSPACE/build`. To record a new
profile after changing the sources in `src/`:

1. Dispatch `PCG toolchain` with `pgo: instrument`; it publishes the instrumented compiler as
   `pcg-lean-pgo-instrumented_<arch>`.
2. Dispatch the `Lean PGO profile` workflow of `pcg-docs` (private, which is why the training does not
   run here) with that commit. It runs the instrumented compiler over the modules in
   `formalization/scripts/pgo-train-modules.txt` on a runner of each architecture and publishes
   `pgo-profile_<arch>`.
3. Commit the two files as `script/pgo/profile-<arch>.tar.xz` and the instrumented commit as
   `script/pgo/profile-rev`.

A profile that does not match the sources of a function is ignored for that function, so a stale
profile only loses speed; the workflow warns when `src/` changed since `profile-rev`.
`script/pcg_pgo.sh` builds the same way on one machine.

## Caveats

- The aarch64 build requires a CPU with the ARMv8.2 extensions.
- Built with GCC rather than the clang used for releases; the profile is only valid for the
  sources and flags it was recorded with.
- `leanc` compiles with the system C compiler (`cc`), because the toolchain does not bundle clang.
