# Native orthogonal viewer review

Current integration checkpoint (2026-09-29): sequential typed navigation/state
and bundled plugin are implemented and locally/installed/live verified. See
[the integration receipt](orthogonal_integration_20260929.md) for current owner,
exact acceptance and remaining scope. The scan gate/native-only statements below
are retained HISTORICAL evidence, not the current implementation disposition.

Base:OpenHCSDev/openhcs main0c7b898f852a8bedc0e1bc38b93f36088d301808.
Tracking issue:#152, native XY/XZ/YZ review through managed viewer MCP.
This is an implementation workstream, not a completed fix.

Observed: the public viewer family provides routed axes navigation, visibility
and camera operations but no native orthogonal display-axis selection. Slider
navigation, projection, X11 injection and private console use are not substitutes.

Extend the existing nominal command/request/state owners and let their current
projection derive MCP exposure. Preserve semantic route coordinates, native
transforms, raw/result/point identity and intensity; reflect orientation and
canvas/camera in review evidence. No parallel controller or mirrored registry.

Remaining: complete NRA dependency/raw-record coverage and declaration-owner
receipt; implementation; non-cubic synthetic XY/XZ/YZ alignment and invalid-axis
regressions; bounded fresh-process isolated/offscreen MCP/viewer proof; review.
Source/native proof and live biological evidence are distinct.

Write scope: viewer command/DTO/service/runtime/state and relevant tests.
Result-directory inspection is a separate workstream. Capability declarations
are a potential crossing: coordinate before shared class/import edits.
The dirty shared checkout, frozen analysis, live UI and viewer remain untouched.

## Investigation checkpoint, 2026-09-28

See [the surface receipt](orthogonal_viewer_receipt_20260929.md) for source
owners, dependency context, measurements, native diagnostic and scan failures.
This remains a proposal, not an implemented or completely audited feature.

Native Napari 0.6.1 sequential XY/XZ/YZ selection passed a synthetic seven-axis
diagnostic, including non-third-last `z_index`, singleton and non-singleton
component dimensions, anisotropic scale, translations, dense Labels and Points.
This is not an OpenHCS managed-viewer, MCP, plugin or rendered-capture proof.

The existing bundled npe2 entrypoint is `openhcs = "openhcs:napari.yaml"` in
`pyproject.toml`; its manifest currently declares the SWC reader and ROI Manager.
Proposed scope: extend that plugin with a typed sequential-plane widget using
the same command and native state owner as MCP. Do not introduce another
controller or copy volume data. Linked simultaneous panels are separate work.

The upstream `napari-orthogonal-views` manager supports more than three
dimensions. Its `update_dims_order` preserves the leading entries of CURRENT
`dims.order` and rotates its final three entries. The issue is semantic axis
selection when those entries include a component such as `well`, not a general
ndim restriction or a fixed requirement on physical data axis positions.

Implementation is blocked before production Python edits: complete NRA/R1 coverage has not
been obtained within the 768 MiB worker scan ceiling. The corrected-budget scan
was stopped at 771 MiB sampled RSS; failed receipts are retained. A larger scan
allowance requires main's direction, and heavy work also requires the host's
available-memory and PSI gates. No scientific or existing viewer work occurred.

## Supported native-only checkpoint, 2026-09-29

The authorised standalone diagnostic is now
`tests/runtime_diagnostics/orthogonal_native_7d.py`. An owned uv environment
resolved and installed pinned Napari 0.9.1 (satisfying `>=0.7.1`) and NumPy 2.5.3
from wheel hashes; shared installs were untouched. The unchanged six-case
diagnostic passed 94 raw/dense-Labels sample pairs and 6 transformed Points
checks. Final descendant-monitored repeat: 5.14 seconds, peak native RSS
161,388 KiB, sampled aggregate plus monitor 186,116 KiB; task disk <1 GiB.

The initial functional pass is retained, but its process-group monitor omitted
the Python child and reported only 1,776 KiB. It is not real-time RSS guard
proof. A PID/start-checked, pidfd-pinned descendant monitor was then verified
against an owned 32 MiB child allocation before the final repeat. Exact helper
source, hashes, failed/successful receipts and sampling limitations are recorded
in [the surface receipt](orthogonal_viewer_receipt_20260929.md).

Main also demonstrated an in-scope closure obligation: result selection uses
the coordinate-axis prefix inferred from `ndisplay`, not the actual hidden
axes after `dims.order` changes. XZ/YZ selection must project the actual hidden
set through the existing typed route presentation; legal XY and truthful
planar Shapes cross-section rejection must remain intact.

No production Python, GUI, plugin or MCP implementation is complete. The
standalone diagnostic exception does not waive the complete NRA/R1 audit gate.
PR #154 remains draft and issue #152 remains open.
