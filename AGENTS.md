This is a fork of the Z3 SMT solver with an improved string theory solver in `src/smt/theory_str_noodler`.

## Decision procedure outline

1. The DPLL(T) framework calls `final_check_eh` at src/smt/theory_str_noodler/theory_str_noodler_final_check.cpp:153 to check the satisfiability of a boolean assignment to relevant string literals.
2. After preprocessing and trying several heuristics, the solver prepares for a more complete search. The search proceeds by iteratively refining the solution space described by a regular constraint (also called automaton assignment) for each string variable until all equational constraints are satisfied.
3. For this purpose, the solver performs a tree search where each node records an NFA assignment and a worklist of one-sided language inclusion constraints that are not yet satisfied. `compute_next_solution_with_len_checks` drives this search by processing worklist nodes. When it finds a node with no remaining predicates, it returns that node's NFA assignment as a candidate; `final_check_eh` then checks the candidate against the length constraints and resumes the search if necessary.
4. The solver calls `process_inclusion(predicate, state)` to subdivide the current NFA assignment in `state` to satisfy `predicate`, generating new nodes. Although some cases can be easy, generally the solver will need to perform a "noodlification" that involves expensive NFA computations.
5. Noodlification is implemented by the third-party MATA dependency. The debug and release presets share the MATA source checkout at `build/_deps/mata-src`; the implementation is in `build/_deps/mata-src/src/applications/strings/noodlification.cc`. The process concatenates each side's NFA assignments using epsilon transitions, intersects the resulting automata, and decomposes the intersection into linear sequences of NFAs ("noodles"). The solver introduces a fresh variable for each segment, then uses those variables to parameterize and substitute the original variables.

## Build & Install

**Do not rebuild the whole project for routine changes or diagnostics.** Reuse an existing configured build directory and build only the narrow target needed; CMake/Ninja will incrementally rebuild its affected objects. Do not create a fresh build directory or temporary worktree merely to test a source change, and do not perform a clean or full rebuild unless the user explicitly requests it or the existing build directory is unusable.

For normal shell iteration, prefer a target-scoped incremental build:

```sh
cmake --build cmake-build-debug --target z3 -j 12
cmake --build cmake-build-release --target z3 -j 12
```

Only rerun configuration when it is missing or genuinely stale, and use an install target only when installation is needed. For initial configuration and installation, use the repository presets:

```sh
cmake --preset "GCC 14.2.0 x86_64-linux-gnu Debug"
cmake --build --preset install-shell-debug

cmake --preset "GCC 14.2.0 x86_64-linux-gnu Release"
cmake --build --preset install-shell-release
```

The presets write build outputs to `cmake-build-debug` and `cmake-build-release`, while both reuse `build/_deps/mata-src`. With Catch2 v3 installed, build and run the debug tests with:

```sh
cmake --build cmake-build-debug --target test-noodler -j 12
./cmake-build-debug/test-noodler '~[e2e]'
```

The SMT-LIB end-to-end tests launch a Z3 shell with a strict one-second timeout per input. The debug shell is not a
reliable baseline for this suite: some cases are known to time out or otherwise fail only in debug builds. These are
long-standing expected failures and should not, by themselves, be attributed to the change under test. Run the e2e
suite against the release shell instead:

```sh
NOODLER_E2E_Z3="$PWD/cmake-build-release/z3" ./cmake-build-debug/test-noodler '[e2e]'
```

An e2e failure with the release shell, or a new failure outside the `[e2e]` tag, should still be investigated.

## Debug

Noodler can be run for a short, reproducible interval with only the structured visualizer trace enabled:

```sh
timeout 10s ./cmake-build-debug/z3 failed_sample.smt2 -tr:z3_visualizer
```

`z3_visualizer` must be the only enabled trace tag. Other trace tags write unstructured text to the same stream and
therefore make it invalid YAML. The trace is written to `.z3-trace` in the process's current working directory; it is
not the solver's standard output. Running another traced solver in the same directory replaces the file.

Due to the large size of the file, you must always run the tool script `scripts/z3_trace_query.py` to extract the
relevant information from it.
