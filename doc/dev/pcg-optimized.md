# The `pcg-optimized` branch

This branch of the fork is v4.35.0 plus changes that reduce the CPU time of building the `pcg-docs`
formalization. It produces the same `.olean`, `.ilean`, `.c` and message output as v4.35.0 (checked
byte for byte, apart from the githash in the `.olean` header, over all 1306 modules that
`lake build` of the library roots elaborates) and passes the `elab`, `elab_fail`, `compile` and
`docparse` test piles (3816 tests).

## Changes

| Commit | Effect |
| --- | --- |
| `IO.appPath` uses the `readlink` length | The result was not NUL-terminated; under valgrind it contained stale bytes and broke every file that compiles a definition. |
| Import resolves the search path entry once per root package | Importing probed every search path entry for every module (about 40k failing `stat` calls per process, which also serialize on directory locks when many `lean` processes run). |
| `lean_mark_persistent` / `lean_mark_mt` skip scalars and persistent objects before the worklist | Fewer worklist operations during import. |
| Compiled form for persistent IR declarations in the interpreter | Imported IR is decoded once per thread; callees, constants and partial applications are resolved once. `LEAN_IR_NO_COMPILE=1` disables it, `LEAN_IR_COMPILE_THRESHOLD=n` compiles on the n-th call. |
| `FixedParams` finds the mutual block of a call by hash | The analysis scanned every declaration of the block for every application. |
| `replace_rec_fn` takes the callback as a template parameter and uses an open-addressing cache | `instantiate`, `abstract`, ... no longer go through `std::function` and `std::unordered_map`. |
| `lean.skipIlean` (opt-in) | Writes `.ilean` files without references and declarations. |

`script/pcg_pgo.sh` builds the compiler with GCC profile-guided optimization. The release used
`-march=armv8.2-a` (inline LSE atomics) for both builds and a training run over 118 project modules
that exclude the five benchmark modules.

## Measurements

Callgrind instruction counts (`valgrind --tool=callgrind`, one `lean` invocation per module as Lake
runs it, imports and options from the module's `.setup.json`):

| Module | v4.35.0 (gcc build) | `pcg-optimized` + PGO |
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

## Caveats

- aarch64 only, and the PGO build requires a CPU with the ARMv8.2 extensions.
- Built with GCC rather than the clang used for releases; the profile is only valid for the
  sources and flags it was recorded with.
- A toolchain installed with `cmake --install` needs `libuv.so.1` (runtime) and `libuv.a` (linking
  executables) next to `lib/lean` when libuv is not a system library.
