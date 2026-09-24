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
documentation, MCP, and TIFF-output tests passed. At this initial review,
the separate published-dependency readiness gate remained open because the
PolyStore change had not yet been released.

The first CI pass found three Black-only formatting differences. After running
the pinned formatter, the changed materialization owner files differ only in
line wrapping. I rechecked the complete analysis-consolidation, ROI, and storage
pages against those unchanged semantics before refreshing their three affected
authority digests. The reformatted test file is not a recorded audit authority.

## Published-dependency follow-up

PolyStore PR #11 was merged and released as v0.2.19. Its publish workflow
passed, and both the wheel and source distribution are present on PyPI.
OpenHCS now requires `polystore>=0.2.19,<0.3` and pins the PolyStore
submodule to release commit `0efe67fdd14985bf90cee6e0f0c4735d41d265d1`.
The 17 documentation audit entries that depend on `pyproject.toml` were
rechecked against the new dependency floor and their authority digests
refreshed. No affected explanatory page asserted the prior floor.

The subsequent website CI run exposed an eager import in the gallery catalog:
its source-capture request used `ExecutionConnectionSpec` only as a postponed
type annotation, but importing that DTO loaded the scientific runtime into
the deliberately minimal website environment. The import is now restricted to
type checking. The gallery's runtime declarations, capture behavior, and
published projections are unchanged. The 13 audited pages referencing the
gallery catalog were checked for claims about those surfaces, and their
authority digests were refreshed.
