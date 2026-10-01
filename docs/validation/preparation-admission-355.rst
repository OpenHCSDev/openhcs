Cold-start preparation admission and selected demand
====================================================

Source owner: Schrodinger/Codex, existing OpenHCS PR358, existing worktree
/home/ts/wt/openhcs-gui-cold-connect-355-20261001. Production checkpoint
ffba8426c, normal continuation of a7137afe1; main integration remains parent-owned.
No new worktree, environment, installation, provider, native/UI/MCP launch,
science replay, shared validation lock or dependency mutation occurred.
Original full-context R1 failure remains unchanged and separately unqualified.

Required relation and source witnesses
-------------------------------------

PreparationCacheBatch.populate_child_caches previously admitted four child
slots independently of process affinity or the configured worker limit.
The original journal lists 30-plus sequential completions, NOT 30 concurrent
workers. Parent reports native preparation209s on tasksetCPU0 and a simultaneous
managed-viewer5992 observation failure after30s. Neither observation identifies
a dominant cost or proves startup contention caused issue385. Separate5994
success also differed in source context; historical5992 identity/exit stays
unproved. The managed-viewer issue is385, not386.

RegistryService.prepare_in_current_process explicitly warmed all catalog
callables, including those absent from the user's compiled workflow. Existing
PipelineCompiler -> prepare_compiled_context_callables -> invocation resolver
-> CallablePreparation already prepares selected invocations before publishing
the compiled bundle. ModuleRegistryPreparation and compiler-prepared registry
families retain their original dependent obligations; this does not prune a
family's required kernels or invent a selected-function registry.

Ownership and deleted duplication
---------------------------------

28 production lines deleted, 28 added in this continuation. IMPL-12: delete the
startup all-callable cache/preparation loop in place rather than copying a new
bootstrap or warmup loop. RegistryService continues to own discovery and its
original authoritative metadata cache. FunctionCatalogPreparation retains the
same future, main-thread metadata preparation, failure/cancellation and strict
catalog-before-serving gate. Status/docstrings now distinguish metadata from
kernel readiness. Catalog readiness does not claim arbitrary kernel readiness.

PreparationCacheBatch remains the sole cache scheduling owner. PipelineCompiler
passes its existing configured/debug-admitted num_workers through the compiled
context preparation owner. The default is serial; serial budgets or fewer than
two allowed CPUs do not launch cache children or even project their work.
Parallel capacity is min(configured worker budget, current OS affinity).
The existing exit-stack/wait/refill/exact-worker cleanup algorithm is retained.
Missing OS affinity support denies optional child parallelism; it does not
guess host capacity or introduce a compatibility facade. Query failures other
than absent support propagate. The original required parent preparation always
runs, and only successful process-local obligations enter the original
PreparationOperation completion set.

This is CPU-affinity plus explicit worker-budget admission, NOT a general
runtime RAM/cgroup-quota estimator. No heuristic RSS multiplication or mirror
of runtime policy is introduced. Installed operation under its real resource
limits still requires parent acceptance. Discovery/reflection cost remains;
selected module/family preparation can still be costly at compilation.

IMPL-1/3/4/5 and MEMB-1/2: no consumer string/enum/concrete-type dispatch, copied
catalog, mirrored completion store or hand-maintained family roster is added.
Existing CallablePreparation/PreparationOperation and compiler-prepared family
declarations own behavior and identity. No new production inheritance is needed.
TIME-1/3/9: the eager kernel path is deleted, not retained behind a feature flag,
wrapper or legacy reader. No persisted store shape or external format changes.
This manually authored source change is not an NRA native equivalence proof.
Full/global85-detector R1 is still unqualified; do not replay the original scan.
Original pinned R0 passes at main7640fd951 -> ffba8426c (23.24s / 87468KiB),
5210 projections and zero positive deltas. Its only nonzero measure is the
previous ZMQExecutionClient GodClassExcess -46. Original Python3.14 tool at
comms-ratchet-pinned-ui348-20261001 / 3b03785f runs unchanged with the read-only
metaclass backing path, not a copied detector. This R0 is not full R1.

New declaration/capability evidence
-----------------------------------

test_preparation_admission declares a new cache operation and independent
AdmissionAudit capability. Empty AuditBefore/AuditAfter leaves compose the
capability on both sides of the operation in genuine C3. Cooperative matching
super hooks execute once in the measured order, with no scheduler/consumer
changes. Existing PreparationOperation owns successful preparation sharing;
the shared scheduler owns budget, refill and cleanup. Synthetic workers exercise
seven obligations under two/three slots without real parallel children, including
failed refilled work and unchanged parent readiness. Affinity1 and budget1
deny children before admission hooks. A selected compiled callable's hook runs
once; an unselected catalog hook never runs. Failed selected compilation retries
its required hook instead of publishing a successful completion.

Bounds, preserved failures and validation
-----------------------------------------

Startup helper warning2: RAM19.7GiB/home15.5GiB free, swap13.9GiB, root7.9GiB.
One serial source test process at a time, CPU0/thread pools1, kernel512MiB/no
swap and outer60s. Exact read-only Python3.12.3 interpreter:
/home/ts/wt/openhcs-generated-inputs-installed-parent-20261001/.venv/bin/python.
No package installed/copied. The source-only native extension import uses that
existing environment's openhcs/core path, without invoking image processing.

All command lines and resource outcomes are retained in preparation-admission-
evidence; full resource commands include source selection and test paths.
Environment: PYTHONDONTWRITEBYTECODE=1, PYTEST_DISABLE_PLUGIN_AUTOLOAD=1,
OPENHCS_CPU_ONLY=true, OMP_NUM_THREADS=OPENBLAS_NUM_THREADS=MKL_NUM_THREADS=
NUMBA_NUM_THREADS=1; XDG_CACHE_HOME/TMPDIR and NUMBA_CACHE_DIR point only into
/home/ts/.cache/agent-scratch/openhcs-preparation-admission-355-20261001.
systemd-run --user --scope uses MemoryMax=512M MemorySwapMax=0 CPUQuota=100%;
timeout --signal=TERM --kill-after=3s 60s wraps taskset -c 0 and Python -I -B.
Pytest uses --noconftest, -oaddopts=, no cacheprovider and owned basetemp.

Initial red collection failed because the source checkout lacks the installed
_tabular_native extension (exit2, 1.52s / 85356KiB); preserved before.log.
With the read-only extension path admitted, original source is red:14 failures,
1 pass (2.01s / 89320KiB), including actual default four-slot admission and
execution of the unselected hook, not just the new budget argument contract.
That initial15-case declaration was subsequently extended to19 current cases;
the red transcript is retained as the original experiment, not recomputed.
Initial repaired selection:20 passes (5.72s / 234212KiB).

Broader mixed-dependency shard timed out60.02s / 352020KiB, exit124 in the
existing GUI cancellation test. Its installed basicpy backing ZMQRuntime lacks
the PR13 EndpointConnectionAttempt.connect_async method required by reviewed
PR358. Source inspection established that mismatch; do not count the run as
passed. Its inputs/log remain retained. No native child/runtime was launched.
The corrected selection explicitly uses paired ZMQRuntime source aca18eaf2
(production a9d4ddd):59 passed,6 skipped,2 pytest configuration warnings,
6.97s / 350600KiB, exit0. All six skipped tests require two/four admitted actual
fork slots; CPU0 cannot provide them. Multi-slot source scheduling/MRO/failure
behavior is covered with synthetic workers, not claimed as native concurrency
qualification. Original dependency35+new lifecycle13 are separately retained
in PR13's issue385 receipt (56 source cases across that selection).

Focused source-owner cProfile:19 passes,3.22s / 107624KiB, exit0. It exercised
20 cache-population calls,4 selected compiled-context preparations and4
metadata preparations through the actual shared owners. This is a synthetic
work-routing profile, NOT a profile of the historical209s warmup and NOT proof
of its dominant cost or an installed latency improvement. Full native-thread
environment keys were1 and configure_native_thread_count(1) applied before
the experiment; loaded pool observations were openblas1/openmp1/openblas1.
The profile command and selected owner call counts are retained verbatim.

Remaining acceptance and exact cleanup
--------------------------------------

Parent owns paired OpenHCS managed-viewer adaptation to the published shared
EndpointProcess contract, installed preparation profiling/cold-connect tests,
selected real compile/run, viewer stream/bitmap/exact-close and serialization
with Dalton's active environment. PR358 gitlink remains23097e26 until paired
viewer migration; no unmigrated typed contract is installed. Source passing
does not prove lower real cold latency, the frontend --help cost, issue385
resolution, biological quality or full/global audit completion.

Cleanup: canonical owned root
/home/ts/.cache/agent-scratch/openhcs-preparation-admission-355-20261001,
1728KiB measured. Terminal process and no-open-handle checks and retained log
checksums passed before removal; the exact directory was removed and verified
absent afterwards. Compressed R0 decompresses to the same raw
SHA256 b8328607e5048099c9eb7749b0b932f59857cfb7dbb0a27dd2cd556a19fb6aac.
Original failed scientific/parent evidence, source and durable history remain.
