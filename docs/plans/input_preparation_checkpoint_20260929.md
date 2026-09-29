# Input preparation checkpoint

Implementation owner: Lovelace. Integration owner: OpenHCS coordinator.
Branch: `fix/input-preparation-20260929`.
Worktree: `/home/ts/wt/openhcs-input-preparation-20260929`.
Issues: #172 and #132.

## First checkpoint: #172

Zero pixel overlap uses unrestricted cell positions, not empty random ranges.
Zero stage error uses exact grid positions, without consuming jitter draws.
Both layouts share the existing generator's tile-position behavior. Positive
jitter retains the original MT19937 sequence. No parameters are replaced with
nonzero defaults.

Focused generator regressions cover ImageXpress and OperaPhenix, native and
vendor metadata, 1x1 and 2x2 grids, requested counts, deterministic pixels and
subpixel overlap. The existing randomness controls are retained.

The continuous MCP regression uses the current real stdio entrypoint, generates
the issue's 1x1/64px/one-channel/one-Z/four-cell/A01/seed7 plate, inspects it and
samples pixels. It does not replace the transport, services or workspace owners
with mocks. It does not use a GUI, biological input or a paid provider.

## Continuing scope: #132

Push known physical path selections ahead of unrelated store opens using the
source declaration and its existing filter matcher owners. Metadata and axis
selection remain at decoded plane projection. Synthetic tests measure opened
entrypoints and exact projected references; no real 16-CZI run is authorized.

Contour extraction and ImageJ ZIP encoding belong to the recorded PolyStore
submodule. Coordinate permission before changing it. Fragmented labels are
parent objects with many shapes; ZIP member count is not a biological count.
Remaining work: fragmented fidelity/profile receipt and bounded repeated-work
improvement, review of companion-file selection, coordinator installed journey.

## Validation and resource boundary

All eight dependency imports were verified under this worktree's recorded
submodule roots, using `/home/ts/code/projects/openhcs/.venv/bin/python` and an
explicit worktree/submodule `PYTHONPATH`. No package installation or shared
source change. Main was fetched and integrated normally before implementation.

Focused source evidence: 20 tests passed in 2.32 seconds (zero geometry,
randomness, and preparation selections). This is not a full NRA scan or broad
suite. Source review is limited to the source declaration, store adapters,
workspace handler, synthetic generator and their regression witnesses.

Real current-entrypoint evidence: four continuous MCP health, orientation,
generate, inspect and sample journeys passed in 23.19 seconds. Layouts:
ImageXpress and OperaPhenix, each with vendor and native OpenHCS metadata.
Each returns one requested uint16 image and an 8x8 pixel sample; native
metadata records one image and the requested 1x1 grid. This uses source overlays
with verified imports, not a changed installed package or an installed acceptance
claim. New test files pass Ruff; full-file Ruff reports existing source debt.

The resource guard reported 12.8 GiB available RAM with a swap-only warning
(11.7 GiB used). Only small single-process provider-free checks are run;
large/GUI/JVM work is deferred. Tests/MCP acquire the batch's nonblocking
validation lock. Busy lock means independent source work, not polling.

Scratch owner: Lovelace. Purpose: tiny generated regression plates and pytest
fixtures. Path: `/home/ts/.cache/agent-scratch/openhcs-issue-input-20260929`.
Remove only this owned disposable output after preserving results here.
Source, PR body and evidence stay in the persistent worktree.

No merge/install performed. Installed acceptance is reserved to the coordinator.
Do not close either issue solely from source tests.
