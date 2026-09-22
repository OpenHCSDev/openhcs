# PR #126 authority-delta documentation review

Date: 2026-09-22

## Purpose

PR #126 changes declarations, runtime projections, services, and behavioral tests
that are recorded as evidence for active OpenHCS documentation. The editorial
audit gate consequently invalidated 106 authority edges. This receipt records
the required comparison before those evidence hashes are renewed; it is review
evidence, not a new authority for product semantics.

The semantic owners remain the declarations, implementations, and executable
tests named by each record in `docs/audits/*.json`.

## Scope

The review covered all 51 affected active documentation sources, including the
project `README.md`, against all 30 changed authority files. Those relationships
span:

- 19 edges in `architecture_a_m.json`;
- 39 edges in `architecture_n_z_development.json`;
- 45 edges in `user_docs.json`; and
- 3 edges in `project_surface.json`.

Twenty-eight changed authorities belong to the exact viewer/source-projection
change in `9c5c5b71`; two belong to the neurite/QA guidance change in
`e995f367`. None of the reviewed authority changes was introduced solely by the
formatting commit.

The highest-fan-out owners were `openhcs/core/config.py` (22 dependent edges),
`openhcs/runtime/viewer_protocol.py` (8), and
`openhcs/core/artifacts.py` (7). The most directly affected pages were the
streaming boundary, MCP development, real-time visualization, and viewer
management documents.

## Findings

The current prose already describes the owner boundaries introduced or refined
by this change:

- exact source coordinates and source/group lineage remain typed runtime and
  persisted projections rather than filename- or payload-summary
  reconstruction;
- route-local viewer domains own selection coordinates, including collapsed
  scalar component axes, while shared display domains remain derived views;
- persistent and transient viewers must settle accepted work, while process
  persistence controls lifecycle rather than render completeness;
- process-global Napari launch settings belong to typed streaming
  configuration and compatibility checking; exact fields remain generated from
  the configuration declarations rather than copied into prose tables;
- MCP progress, UI-bridge startup, and caller timeouts remain projections of
  their declaration-owned operation and transport policies; and
- neurite/image-analysis guidance continues to require declared artifacts,
  fixed-coordinate evidence, bounded parameter changes, and explicit
  uncertainty rather than viewer-only conclusions.

No dependent page required a factual prose correction. The review therefore
retains existing findings and dispositions, appends this targeted validation
record, and refreshes only the 106 compared authority hashes.

## Validation boundary

This editorial review does not waive runtime or release gates. PR #126's
current CI separately reports a duplicate source-projection-address failure,
a Fiji missing-`site` viewer projection, and an unreleased ObjectState
candidate. Those fail-loud results remain merge blockers and must be repaired
and rerun. Any repair that changes one of the 30 reviewed authority files must
invalidate and refresh its dependent audit edges again after comparison.

The documentation acceptance command is:

```bash
python scripts/validate_docs.py docs/source
```

The focused ledger regression command is:

```bash
python -m pytest tests/unit/test_validate_documentation_audit.py
```

The figure hygiene review also found 996 newly added trailing-whitespace
diagnostics in the generated Figure 3 SVG. The generator now normalizes SVG
line endings, the retained artifact and provenance digests are synchronized,
and the paper test asserts both whitespace cleanliness and receipt integrity.
