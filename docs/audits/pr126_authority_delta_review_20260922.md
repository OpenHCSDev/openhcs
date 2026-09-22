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

## Integrated repair follow-up

After the initial review, the coordinated repair stack added three commits:

- `83143759b` makes result-image inventory records directly streamable through
  the Image Browser's existing typed path;
- `2d506c180` projects one declared payload-local plane component into exact
  scalar Fiji items before window grouping and rejects malformed, mismatched,
  or conflicting declarations; and
- `1109bafaf` reduces repeated scalar image materializations to the one
  execution scope that owns their complete source address and rejects
  conflicting payloads.

The Image Browser change modifies no recorded audit authority and remains
consistent with the documented ability to inspect source and output references.
The Fiji and scalar-materialization repairs invalidate six recorded edges. The
complete affected Fiji, visualization, storage, and analysis-consolidation pages
were re-read against the four changed owner/test files. Their existing ownership
and failure-boundary claims remain accurate: exact coordinates come from the
typed payload, scalar persistence follows source identity rather than repeated
execution groups, and malformed or conflicting projections fail rather than
being guessed or overwritten. No prose correction was required. Only those six
compared hashes receive a follow-up refresh.

## Released-dependency follow-up

ObjectState 1.1.8 was subsequently published from tagged commit `b0004daf` and
verified as installer-visible. Integration commit `42bcf6e36` advances the
recorded submodule from the reviewed release candidate to that tag and raises
the published dependency floor in `pyproject.toml` from 1.1.7 to 1.1.8. The
owner-package delta after the candidate contains only its release version plus
code-quality and coverage-receipt cleanup; it does not change the reconciliation
semantics reviewed above.

The `pyproject.toml` change invalidates 17 recorded evidence edges. The complete
architecture, development, project-surface, installation, integration, and
compatibility pages owning those edges were re-read against the exact floor and
gitlink changes. Their package-ownership, supported-environment, installation,
and extracted-foundation claims remain accurate, and none states a conflicting
ObjectState version. No prose correction was required. Only those 17 compared
`pyproject.toml` hashes receive this follow-up refresh; the gitlink is not a
recorded authority for these pages.

## Validation boundary

This editorial review does not waive runtime or release gates. At the initial
review, PR #126's CI separately reported a duplicate
source-projection-address failure, a Fiji missing-`site` viewer projection, and
an unreleased ObjectState candidate. The integrated runtime commits address the
two runtime failures, and the released dependency follow-up closes the
ObjectState publication gate. Full integrated CI still must verify the combined
tree. Any later repair that changes a reviewed authority must invalidate and
refresh its dependent audit edges again after comparison.

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
