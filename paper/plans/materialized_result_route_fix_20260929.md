# Explicit materialized result review

Base:OpenHCSDev/openhcs main0c7b898f852a8bedc0e1bc38b93f36088d301808.
Tracking issue:#134. This is an implementation workstream, not a completed fix.

Observed: actual typed measurement outputs carry disk locations outside the
default result directory. Public inventory/existing-file stream does not
resolve that declared directory and fails handler detection or file lookup.

Complete the existing ownership route from materialization identity/location
through authorized bounded CSV/ROI inspection and managed-viewer reopening.
Preserve source/axis/object/provenance and path policy; do not mirror an
artifact registry, relocate files, or rerun scientific analysis. Trace existing
declarations/implementations/consumers before deciding whether to extend the
current request boundary. One shared mechanism, no per-extension dispatcher.

Remaining: complete NRA dependency/raw-record coverage and declaration-owner
receipt; implementation; family-level bounded/path/provenance regressions;
fresh-process synthetic MCP/viewer proof; review and remote publication.
Source/native proof and live biological evidence are distinct.

Write scope: plate/result inventory and inspection service/DTO/tests. Viewer
orientation is a separate workstream. Capability declarations are a potential
crossing: coordinate before altering shared classes or import regions.
The dirty shared checkout, frozen analysis, live UI and viewer remain untouched.
