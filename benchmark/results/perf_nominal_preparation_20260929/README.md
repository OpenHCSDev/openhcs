# Nominal compiler preparation and cross-process kernel reuse

The compiler now consumes declared preparation operations. A public ABC owns
successful completion and failed-operation retry; module and callable hook leaves
retain their distinct identities and inherit hook execution. Registry membership
still comes from the existing registry discovery owner. A generic cache batch
deduplicates operations before checking each operation's public child eligibility.
Parent preparation remains necessary after child cache population.

This is the user-requested structural dependency of further scheduling and cache
work. **It does not make LLVM or numerical execution faster.** The removed paths
were duplicate completion implementations and a registry-specific scheduler;
the backend's separate specialization cache retains its independent lifetime.

The same-source-path, same-cache warm replay on
`ExampleImagingFlowCytometryObjectsInGrid`, one well and one CPU thread, was:

| Preparation implementation | Compilation | Execution job | Total observation |
| --- | ---: | ---: | ---: |
| Baseline | 3.183 s | 20.630 s | 26.532 s |
| Nominal operations | 3.211 s | 20.618 s | 26.553 s |

These single observations establish exercised behavior and show no material
change in this pair; they are not a statistical equivalence or speedup claim.
Earlier and later candidate warm observations are retained rather than discarded.
A deliberately empty-cache candidate took 26.311 s to compile and 50.926 s total.
The few-second cold-compilation target remains open. Preparation accounts for
23.712 of 24.655 seconds in the diagnostic trace. Nested kernel profiling found
5.679 seconds in the 2D intensity quantile kernel, including 4.413 seconds in its
partition helper. Merely reorganizing its caller cannot erase that LLVM cost.

Every retained single-well run produced the identical 11,550,064-byte output,
SHA-256 `3e00436ae1500047fd2605021ae055492b17dbe0b4aa4ddbe2f62af6f8e073be`.
The two-well output has its own hash and is not asserted byte-equal to a one-well
plate. Numerical kernels and scientific output declarations were not changed.

## Compiled kernels are already reusable with spawn

Two genuinely fresh spawned processes used the same populated `NUMBA_CACHE_DIR`.
Each observed **12 dispatcher disk-cache hits and zero misses** while preparing
the intensity and shape families. Family hydration took 0.357 and 0.353 seconds;
starting both processes, importing their dependencies, hydrating and joining took
1.819 seconds total. The parent did not prepare those families in memory, so this
is disk reuse rather than inherited fork state.

An ordinary two-well, two-process-worker spawn pipeline also completed:
compilation 3.651 s, execution job 28.581 s, total 34.869 s. Its endpoint log
contains 139 cache-data loads and zero cache writes. This supports reuse of the
observed cache-enabled kernels; it does not prove that every possible execution
path avoids JIT or that uncached Numba functions never compile. Issue #162 remains
open for the broader preparation/timing boundary.

The single-worker resource is an inline lane. A configured `fork` or `spawn`
start method does not itself establish that an execution child was created.
The separately retained `spawn-configured-single-inline-lane` observation is
explicitly excluded from the proof of actual spawned execution. Cold compiler
cache population can still create up to four fork children independently of
the one-thread execution setting.

Numba's existing cache validates code, signatures and compatible runtime/CPU
identity. Keep one persistent cache for compatible runs; changing the cache root
for a deliberately cold measurement is a separate workload. No second kernel
cache or handwritten specialization roster was introduced here.

## Source and validation

The ownership receipt is [ownership_decision.md](ownership_decision.md).
NRA was fetched into a clean isolated worktree at `0844525`, preserving the user's
dirty original checkout. Its packaged `nra-refactoring` skill was read; the exact
named `refactor-audit` skill was not found and is not claimed to have been used.

The class-first census covered all 696 original modules and 5,014 classes, with
5,002 canonical projections. After introducing the operation module it covered
697 modules and 5,022 classes, with 5,010 projections. The same 12 conditional or
function-local classes remain OPEN. The full semantic scan exceeded its explicit
165-second budget. Completed bounded raw scans covered four before/five after
modules and retained the same two unrelated heuristic leads: a constructor
validation check and a runtime output-context condition. Neither was deleted.
There were no mapping/record-shape findings in those bounded scans. This is not a
complete whole-package semantic audit.

NRA applied exact authored target patches and the new-file declaration through
revision-checked transactions. Configured guards reject the retired helper calls
and scheduler attributes. A subsequent refinement had source preflight but no
equivalence guard suite. Syntax and guard results are distinct from behavior:
**294 local tests passed**, including real fork PIDs, parent readiness, hook
replacement, delayed metadata effects, failed-hook retry, equivalent bound-method
identity, and a new operation without a scheduler roster. Black passed all six
changed files; Ruff introduced zero new findings (37 baseline, 36 candidate),
and the new module/tests pass Ruff cleanly.

Benchmarked ownership baseline: `213439a04` plus the recorded candidate source
hashes. Latest-main validation also includes `8b090e2e9`. The raw observations,
run-input fingerprints and paths are in [observations.csv](observations.csv),
output hashes in [output_parity.csv](output_parity.csv), and source/scan evidence
in [provenance.json](provenance.json). The retained cache counters are
[spawn_cache_hits.json](spawn_cache_hits.json). Run
[probe_spawn_cache.py](probe_spawn_cache.py) with the same populated cache and
source path to repeat the bounded spawn probe.

Latest main exposes new PolyStore cache declarations through the MCP/UI
child-environment helper. The old shared editable lacked them and raised
`AttributeError`; the ordinary ZMQ benchmark did not call that helper and still
succeeded. An initial isolated pinned-dependency replay is retained as historical
evidence, rather than used as a substitute for updating the shared installation.

The shared OpenHCS checkout was subsequently synchronized to main `8b090e2e9`,
preserving its previous branch. All eight clean dependency checkouts now match
main's recorded revisions, including PolyStore
`c16b8fc99a07f17e92e5fbf46f312d73cc9c46d7`. They and OpenHCS were reinstalled
editable with an eager upgrade to the latest versions allowed by their declared
requirements (`dev,gui,cellprofiler-compat,bioformats`). `pip check` passes.
Actual loaded paths and revisions are in [shared_environment.json](shared_environment.json),
resolved versions in [shared_requirements.txt](shared_requirements.txt).
A real fresh stdio MCP health request succeeded with the shared interpreter;
its receipt is [shared_mcp_health.json](shared_mcp_health.json).

All 294 compiler tests passed again after the upgrade. Environment validation
found an obsolete main test expecting four keys instead of six; PR #231 updates
that expectation using dependency declarations and verifies their consumption in
a fresh child. Its 32 focused tests pass. This establishes the environment and
MCP startup portion of #224, not its full installed plate-inspection/concurrency
acceptance; that issue remains open.

The updated shared-environment replay took **3.267 s compilation, 19.349 s
execution, and 25.377 s total**, with the identical output hash above. The
remaining 2.762 s includes fresh endpoint lifecycle, submission and observation,
result loading, shutdown and benchmark bookkeeping outside the two server jobs.
This later environment observation is not a controlled speedup comparison
against the earlier environment; the same-environment A/B remains the pair above.

Source workspace staging lies outside the observation timer. Execution measures
the completed server pipeline job; total includes fresh endpoint lifecycle,
compilation, execution and observation work. Native CellProfiler was not rerun
for this architecture-only migration, and no new relative-to-CP speedup is
claimed. The preceding measured native scaling report remains separate.
