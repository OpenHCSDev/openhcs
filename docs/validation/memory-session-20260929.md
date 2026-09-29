# Memory/session issue batch: #131 and #169

Implementation owner: Linnaeus. Integration and installed/live validation owner:
the OpenHCS coordinator. Worktree: `/home/ts/wt/openhcs-memory-session-20260929`.
No saved H001 files, Euler inputs/results, installed source, or shared main were
opened or modified. No GUI, JVM, GPU workload, provider or execution server was
started by this worker.

## #169: declaration and runtime ownership

An unpublished NumPy-decorated function reproduces `TypeError: cannot pickle
'_thread._local' object` in both `dill.dumps(function)` and a real ObjectState
history export. Its `__globals__` belongs to `arraybridge.decorators`, while its
declaration module belongs to the source execution namespace. Dill therefore
serializes decorator globals by value, including `_thread_gpu_contexts`.
Published importable functions and plain current global/UI/pipeline configuration
history do not reproduce the failure. This is a reproduction of the reported
failure mode, not reconstruction of the disposed H001 in-memory graph.

The existing ArrayBridge `ThreadGPUContext` now owns its thread-local storage.
Decorator globals carry the importable runtime owner, not its runtime handle.
There is no history filtering, alternate registry, permissive pickle handler,
legacy reader, or change to ObjectState's durable document format. The obsolete
global storage and forwarding function are deleted. GPU invocation uses the
same context/stream behavior through `ThreadGPUContext.current()`.

Regression coverage includes unpublished CPU/GPU-decorated callable persistence,
stable isolated per-thread contexts, and a continuous native document/history
save, fresh-registry load, historical undo and return to current declarations.
The retained runtime context is populated with an unpickleable thread-local
handle and must remain alive and identical. The native history test uses real
pipeline document, scope and ObjectState owners; it is not desktop live proof.

The minimal repaired callable round trip executed successfully (14,424-byte
payload); its restored NumPy result was `[0, 1]` for thresholding `[1, 4]` at 3.
The paired upstream's three focused decorator/context tests passed (0.15s),
and changed-source Ruff/diff checks passed. The OpenHCS native regression and
real desktop journey are pending at this initial checkpoint. Paired upstream
draft: https://github.com/OpenHCSDev/ArrayBridge/pull/1.
H001 was already closed by explicit owner disposition;
there is no request or authorization to recover its lost history.

## #131: bounded retention diagnostic

`benchmark/mcp_memory_diagnostic.py` constructs the real full-surface OpenHCS MCP
server and reserves the actual stdio transport. One harness-only tool samples
that disposable process, optionally after `gc.collect()`. It does not replace
the UI, application, capability services or protocol path with mocks, and does
not add a diagnostic capability to production MCP.

The receipt records PID, monotonic time, RSS, PSS, private clean/dirty, swap,
threads, imports/native libraries/frameworks, catalog/custom declarations and
ObjectState snapshots before/after every operation and after full GC. Repeated
read-only health/authoring/capability queries are measured after a separate
warm-up round. Per-round slopes describe this sequence only. Flat measurements
cannot prove catalog/compile/custom-source/execution/GPU/JVM paths leak-free;
positive slopes alone cannot establish causation or a leak.

Run only with the validation slot and at least 8 GiB available RAM:

```sh
flock -n /home/ts/wt/openhcs-issue-batch-20260929/validation.lock \
  /home/ts/code/projects/openhcs/.venv/bin/python -m benchmark.mcp_memory_diagnostic \
  --rounds 4 --output docs/validation/mcp-memory-receipt-20260929.json
```

Set `PYTHONPATH` to this worktree and its recorded submodule `src` directories,
and verify imported paths before running. The diagnostic owns temporary XDG
data/cache/config and stderr under
`/home/ts/.cache/agent-scratch/openhcs-issue-memory-session-20260929/mcp-*`.
Each run removes that disposable directory on success or failure, retaining the
JSON receipt and bounded stderr tail at the requested output path. The harness
enforces an 8 GiB available-RAM floor, 2 GiB server RSS budget and 180-second
overall timeout.
The diagnostic has no access to another server's process lifecycle; transport
teardown affects only its own fresh subprocess. No services or tmpfs data are
removed to influence results.

## Boundaries and remaining scope

- Source review/AST coverage is focused on history serialization and the new
  diagnostic. No full NRA scan or global architecture-clean claim is made.
- ArrayBridge source-path verification and the minimal reproducer/repair ran in
  the existing environment. Initial combined test collection exposed duplicate
  `tests.conftest` package names across repositories; run the two repositories
  separately. No test assertion was weakened.
- Resource guard reported about 12-13 GiB available RAM but exits 2 for existing
  host swap pressure. Large validation is deferred, and the nonblocking batch
  lock has been busy during attempted focused runs. No unrelated cleanup occurs.
- Coordinator must serialize a new desktop capture/restore and verify the paired
  installed entrypoint after review/integration. No worker merge/install and no
  extra display use are authorized. Neither issue is marked Closes at checkpoint.
