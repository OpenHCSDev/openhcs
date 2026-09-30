# Execution-thread profiling correction (#241)

CPython 3.12 cProfile monitoring previously mixed polling-thread events into execution stacks and omitted compiled Numba calls. This invalidates those old profiles as optimization attribution evidence. The existing policy now inherits one common lifecycle and filename algorithm; runtime-specific leaves bind monitoring callbacks or use native thread-local scope. The environment owner enables Numba events at package bootstrap only when worker profiling is requested.

117 focused and integration tests passed. The concurrent normal/error regression fails twice on main 3032958ac and passes with the correction. Lease cleanup, setup failure, a subsequent profile, child environment projection and fresh-import compiled-kernel accounting are exercised. A production one-well run records zero foreign polling entries and positive compiled-kernel timing. Its output CSV SHA-256 remains `3e00436ae1500047fd2605021ae055492b17dbe0b4aa4ddbe2f62af6f8e073be`.

The instrumented production execution took 24.154 seconds (30.100 total). This is diagnostic instrumentation overhead, not a performance baseline or speedup. Ordinary uninstrumented main execution was 18.531 seconds. No ordinary-runtime speedup is claimed for this correction.

The NRA census covers 699 production modules and all original ClassDef nodes. Role excerpts retain all original/projected counts and unprojected OPEN classes; they are source-structure evidence, not a proof of behavioral equivalence. The authored exact-source transaction checks the initial staged bodies; subsequent abstract-parent/runtime-leaf refinement is validated by tests and the final census. CPython 3.12.14 / Numba 0.67.0 were physically exercised. The pre-monitoring Python 3.11 leaf preserves native behavior but was not physically run on Python 3.11 here.

After merging current main b48fab2bb (custom registration admission), 122 integration tests passed on the combined source.
