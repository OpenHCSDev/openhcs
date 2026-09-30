# Distinct attempt03 preparation (no execution acceptance yet)

Parent explicitly authorized a new finite native workflow after attempts01/02
were terminal. The BLOCKED S1 goal is untouched. Main642821c was integrated
normally at2e7588546; fixture SHA256 remains
9b737ed5e669c6f2325cc4af9ebb0b39b706121478149315474f464e3cc30c80.
ZMQ28d9ed6 and metaclass448cdf07 pins unchanged; no installed/skill change.

Correct the earlier classification: attempt02 returned a reduced stack under
MainFlowStackOutputSpec's complete-stack promise. Its failure is real, but does
not prove a product defect under a valid declaration. Original job, raw receipts,
source, fixture and outputs remain unchanged. Merged PR272 instead uses existing
MainFlowPlaneProjectionOutputSpec/SelectedPlaneImageOutput for selection, then
complete-stack inspectors for image/labels/measurements. No guard is weakened.

## Registration and source ownership

Original CustomFunctionManager._prepare_source rejects the whole two-function
fixture: exactly one decorated processing declaration is required. Each explicitly
named fixture function is now projected with Python inspect.getsource, importing
its original fixture-owned dependencies. Names come from the explicit callables,
not a new source parser. The canonical manager verifies each source before live
dispatch without persistence. Two reviewed declarations mean two registration
requests, exactly once each after the same preparation handle reports READY.
No competing source namespace/helper registry or direct file publication.

## Exact intended workflow and readback

Twelve ordinary FunctionSteps: selector + inspector + chained inspector for
each of four cumulative selections. Source plane sequences are `(0,1,2)`,
`(2,0,1)`, `(2,0)`, `(0,)`; final singleton remains a one-plane3D stack.
Original step-local LazyProcessingConfig selects Z; PipelineDocument remains
complete and lazy. Artifact-plan inspection must report12 steps and1 native axis.

Readback uses existing observation export, metadata projection decoders, artifact
kind declaration, OpenHCSPlaneAddress and ROIArchiveSourceMetadata. Require every
planned primary plane AND named image-artifact plane, not just len(selected planes).
Every durable CSV row must match all five source coordinates plus exact object
subject, slice index, label and area. Original image/labels/provenance/typed rows
and reopened ROI identities are checked for first and chained inspectors. Exact
image/CSV/ROI inventories are checked, including final main output, with no missing
plane/file fallback. This is diagnostic code, not a new production materializer.

Provider-free command at merged source plus diagnostic changes:
existing venv python -B -m pytest -o addopts=''
tests/unit/agent/test_owned_bootstrap_readback.py
tests/unit/test_volume_projection_fixture.py -q
Explicit worktree PYTHONPATH, CPU/headless, thread1, shared Fiji cache/downloadfalse.
Actual result: **17 passed in1.49s, exit0**. This does not establish compile/native,
installed or biological acceptance. New-case witness: adding a declared image
requires its named projection automatically; deleting either primary or named
planes fails. Each corrupted CSV coordinate fails even when slice/label/area match.

Focused ownership review: BOUND-2 original decoder/address owners retained;
IMPL-4 complete existing projection family consumed; IMPL-13 original launch/close
owners unchanged; IDEN-8 exact original ProcessIdentity retained. No broad/global
NRA scan or passing introduced-debt ratchet claim. +15/+32 god-class remainder
remains archive-owned unfinished work, not waived by this fixture.

Native run remains one distinct allocation with nonblocking validation.lock,
fresh headroom checks, RAM>=8GiB, historical-swap-only exception,80MiB scratch,
240s total journey and10s ordinary observations. On failure/uncertainty preserve
the same handles; no replay. No GUI, installs, downloads or foreign close.
