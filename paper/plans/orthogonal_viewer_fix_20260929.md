# Native orthogonal viewer review

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

Implementation is blocked before Python edits: complete NRA/R1 coverage has not
been obtained within the 768 MiB worker scan ceiling. The corrected-budget scan
was stopped at 771 MiB sampled RSS; failed receipts are retained. A larger scan
allowance requires main's direction, and heavy work also requires the host's
available-memory and PSI gates. No scientific or existing viewer work occurred.
