ASSISTED-2 selected-plane output fails during viewer-enabled artifact finalization

Named source owner: Lorentz. Integration/installed acceptance: parent; no change to live wheels or scientific callable.

Original installed reproducer is retained at `neurite-development-skill383-20261001/output/ASSISTED-2-MATERIALIZATION-DEFECT.rst` in the parent evidence root. Compile completed; execute `71243f96-be49-4fb5-b3b2-65507d868498` failed on 2026-10-01 19:02:57 UTC after the callable returned:

```
Viewer stream singleton plane axis requires exactly one exact component value from the declared plane components; got () from ().
```

Stack: runtime artifact materialization -> saver -> ViewerStreamBackendCallKwargs._output_fields -> StreamImagePayloadMetadataProjector.item_fields_for_plane_components -> _singleton_plane_component_values.

The public SelectedPlaneImageOutput contract retains explicit selected source provenance and a leading singleton image plane. Singleton provenance has no varying component values; the stream projector currently asks artifact storage axes (empty for these declared TIFF stacks) to identify this pixel axis. This is a source/materialization failure, not biological acceptance. Candidate1b disables streaming and materializes completely; scientific candidate disposition remains independent.

Acceptance: source synthetic regression through the actual materialization/public declaration path; all declared outputs persist with selected-plane QA stream metadata retaining exact source identity and 1.3556 calibration. Preserve missing/ambiguous non-singleton rejection controls. No default CHANNEL, fabricated plane identity, suppressed validation, duplicate metadata carrier or registry. PR394 owns shared materialization/runtime image projection files; this work starts in the unclaimed stream projector and new regression tests. Parent owns later installed/live acceptance.
