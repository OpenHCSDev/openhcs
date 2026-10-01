Runtime repair #342 source receipts
==================================

Owner: H003g runtime repair worker under parent integration; draft PR #344.
H003g is permanently FAILED. These are synthetic source checks, not a trial
retry, installed acceptance, result QA or biological success evidence.

Runner: run_source_tests.py. It prepends this worktree's Python source and
uses only the unchanged installed _tabular_native.abi3.so from
/home/ts/wt/openhcs-s1-installed-parent-20261001. Existing dependency packages
are reused without any download, build, install or configuration change.
All execution shards use CPU affinity 0, one CPU quota, 512 MiB MemoryMax,
zero swap, 60-second timeout, OPENHCS_CPU_ONLY=true, numerical threads 1,
and PYTEST_DISABLE_PLUGIN_AUTOLOAD=1. Two unknown asyncio configuration
warnings are expected because optional pytest plugins are disabled.

Final receipt interpretation
----------------------------

merged-main-final-family-controls: 111 PASS, including 15 added full-stack
tests plus 96 existing executor/projection/alignment/device/registry controls.
merged-main-consumer-regressions: 45 PASS, including the unchanged-main ABI
fixture corrected using the real diagnostic declaration owner.
r0-merged-main-openhcs/scripts/benchmark: all PASS. Base main 7b0ec3f5,
head b7702664, exact three changed production paths. Subsequent edits affect
only tests/documentation/receipt packaging, not production sources.

r1-original: import failure BEFORE scanning. The existing current NRA
environment does not export RedundantTypeCheckDetector at the original
guard's import site. Worktree external gitlinks are uninitialized as well.
No passing R1 certificate or complete dependency-context audit is claimed.
nra-before-corrected: deadline_incomplete structured report with null counts,
20-second CLI deadline, parsing unfinished. Its admitted candidate external
directory is uninitialized. This is NOT a successful no-findings report.

Unsuccessful receipts remain in the archive: first-repair slotted-dataclass
super error; family-controls fixture argument and named bundle failure;
family-controls-corrected mask-domain failure; complete-owned-families
temporary metadata deletion error; frozen-executor-reproducer expected exact
float(AlignedImageStack) failure using original executor 20ca4f825 with empty
kwargs; provenance-contract-regressions stale diagnostic ABI fixture;
unchanged-main-abi-fixture confirms that failure on full unchanged main
0c0563e65; final-consumer-regressions nonexistent test paths/zero tests;
r0-original interpreter/dependency import failures; and nra-before incorrectly
admitted root. Earlier passing checkpoints are retained, not substituted for
the merged-main receipts. Logs contain exact original argv and time/RSS/exit
status, and JUnit files contain test identities and timestamps.

Materialization scope
---------------------

The actual shared ABC algorithm owns pixels, masks and typed provenance.
Dense stacks, same-slice bundles, aligned runtime stacks and named output
bundles inherit it, with small axis/domain hooks. Existing nominal registry
dispatch adds full-stack projection for primary images and image kwargs;
other declared runtime families keep their own domains. No name switch,
np.asarray fix, mirrored registry/store or copied executor is shipped.

The MRO cases use two independent test-only capabilities over the actual
composition owner: pixel offset and validity-mask creation. Both cooperative
super orders verify exact pixel and mask effects. They are not a claim of
production MI implementation or whole-package semantic equivalence.

Artifact authority / bounded source replay
------------------------------------------

SHA256SUMS in this receipt archive covers all raw receipt files, the runner,
the five final changed Python files and the architectural source receipt.
Verify it after extracting into the reviewed source worktree. No science
input or trial output is included. Archived original stdout is byte-preserved;
whitespace within tracebacks is not normalized.

Use the original runner and final log argv under the bounds above. To obtain
the expected pre-repair executor failure, set BASELINE_EXECUTOR_REF=20ca4f825
and select only test_real_rescale_full_stack_materializes_composed_runtime_sources.
For a full unchanged-main baseline, git archive the recorded production and
fixture paths and set SOURCE_BASELINE_ROOT to the owned extracted directory.
No MCP/native/viewer startup is part of either source replay.

R0 package: existing cached agent-comms package corresponding to original
CI pin 3b03785f45df2ef5dc62ba6aed99294192ecbb01. debt_ratchet.py SHA256
e323c94d49c2b72d9524a5169f123e64b4a6e46a41035ca9fb4497e49b6ca562;
direct DeclaredFamily/FieldCodec/MroDispatch sources compare byte-identical.
The successful entrypoint uses /usr/bin/python3.14 and existing local
metaclass-registry source, matching the workflow interpreter, without install.
Original R1 source/script is unchanged; its environment failure is retained.

Disposable scratch ownership
----------------------------

Only owned scratch h003g-runtime-repair-baseline-20261001 under
/home/ts/.cache/agent-scratch was used: 31 MiB unchanged-main source archive,
recoverable from Git. Its process completed and its failure logs are preserved
before cleanup. The attempted r1 scratch path was never created (import failed).
No native/viewer/MCP process, lifecycle lock or shared slot was acquired.
Parent owns installation/integration and actual synthetic installed acceptance
after #338. Held-out/reference data and frozen H003g remain sealed/unmodified.
