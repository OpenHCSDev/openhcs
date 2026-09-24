# PR #129 TIFF compression authority-delta review

Date: 2026-09-24

The opt-in disk-TIFF writer change invalidated 34 recorded authority edges
across 29 active documentation pages. I re-read each complete dependent page
against the changed OpenHCS declarations, runtime path, and tests, and the
PolyStore codec declaration. The generated configuration reference remains the
authority for exact fields, accepted values, and defaults; it is not duplicated
as a hand-maintained field table.

Two pages needed prose changes. `concepts/storage_system.rst` now explains the
separation of disk TIFF compression from Zarr compression and semantic
materialization. `guide_for_biologists/configuration_reference.rst` now names
the `TiffConfig` family and its scope in the practitioner mental model. Both
remain explanations rather than becoming exhaustive field references. The
other 27 pages retain their existing claims and Diátaxis purposes: the new
config is resolved from the existing pipeline declaration, carried in the
compiled processing context, and used only on disk TIFF writes, so their
descriptions of inheritance, runtime ownership, ROI, MCP schema projection,
analysis, and viewer behavior remain accurate.

This is an editorial receipt, not product authority. The authoritative files
are the declarations, implementations, and tests recorded in the JSON audit
entries. The changed page and authority digests were refreshed only after this
comparison. Documentation validation passed for 155 audited sources, the full
Sphinx HTML build succeeded with warnings treated as errors, and 15 focused
documentation, MCP, and TIFF-output tests passed. These checks do not waive
the separate published-dependency readiness gate; PolyStore's new source has
not been published as a new release.
