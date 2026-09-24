# Windows source-path authority review (2026-09-23)

The previous PR #128 CI run failed the new two-well CellProfiler integration
case on Windows 3.11 and 3.13 before compilation: `urlsplit` interpreted an
absolute `C:\...\Translocation_doses_and_controls.csv` as URI scheme `c`.
Both failing jobs reported the same source-binding exception. The shared
source resolver now classifies Windows drive-absolute paths as local paths
before URI dispatch, while preserving `file:` and HTTP handling and rejection
of unsupported schemes. Both imported metadata and ordinary image-plane
sources use this owner.

Read in full against the changed owner and retained without wording changes:

- `architecture/measurement_equivalence_system.rst`
- `architecture/microscope_handler_integration.rst`
- `architecture/pattern_detection_system.rst`
- `architecture/source_model.rst`
- `development/source_binding_extension.rst`
- `appendices/glossary.rst`
- `concepts/building_intuition.rst`
- `guide_for_biologists/image_sources.rst`
- `reference/dimensionality_and_measurements.rst`

These pages describe nominal source ownership, imported data, benchmark
observations, or measurement families; none states a path rule contradicted by
the new Windows-local classification. Their affected authority hashes were
refreshed in the three audit JSON files. Local checks: 45 source-binding unit
tests, 10 source-view/two-well integration tests, and `validate_docs.py`
(156 files, 26 Python blocks, 155 audited sources) passed. Windows CI on this
new commit remains the cross-platform confirmation; local Linux tests alone
cannot establish that its original `C:\...` failure is closed.
