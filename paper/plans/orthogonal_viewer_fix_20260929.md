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
