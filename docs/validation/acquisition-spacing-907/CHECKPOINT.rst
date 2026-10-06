Acquisition spacing: declared coordinates, not numeric defaults
=============================================================

Singer owns issue907. Reused isolated checkout:
/home/ts/wt/openhcs-context-bounding-20260929,
branch fix/acquisition-spacing-907-20261006, base888756bbd.
No new worktree/environment/PR, dependency change or compilation/catalog edit.
Eight pre-existing foreign gitlink differences and original untracked evidence
are retained and excluded from this commit.

Owner and consumer change
-------------------------

SourceVoxelSpacing owns common-frame projection, reusing CommonRuntimeValue.
Absent or conflicting declarations supply no plate-wide calibration; individual
payload declarations remain authoritative. OpenHCSMetadataHandler and
BioFormatsMetadataHandler decode their existing source metadata for both the
coordinate view and strict physical scalar. The numeric compatibility view is
separate. SourceVoxelSpacing.resolve_physical_pixel_size and its legacy numeric
fallback are deleted, not moved. Explicit physical metadata readers retain the
existing strict get_pixel_size contract. Anisotropic/relative source frames are
preserved without authorizing an isotropic physical scalar.

Existing source_metadata_by_path, ViewerStreamingSource.calibrated_metadata,
the demo metadata publisher and native SourceVoxelSpacing.layer_coordinate_kwargs
consume these original owners unchanged. Unknown native coordinates use identity
scale/pixel units, not invented micrometers. No second unit store or viewer fix.
Catalog: IDEN-1 (numeric compatibility versus physical calibration), BOUND-2
(consume typed spacing), IMPL-12 (one common-frame projection).

AST and qualification
---------------------

inspect_family.py calls original NRA parse_python_module_roots/inspect_modules,
findings=(). Before/after1056 production/dependency modules parsed successfully;
classes/functions/MRO declarations, imports, assignments and calls are retained
in family-before.json/family-after.json. This is descriptive complete parser
context plus selected spacing-family syntax, not a global detector/R1 pass or
dynamic equivalence proof. All current get_pixel_size/source_voxel_spacing
implementations and callers were read semantically before the production edit.

Original source03:27PASS, exit0,10.06s process wall,393652KiB maxRSS, swaps0.
Existing paired interpreter/read-only receiving28 dependency/native backing;
all matching C++ sources checked before native borrowing. Source ownership stays
on this checkout. No installation or dependency checkout mutation.
Original logs:
/home/ts/wt/openhcs-issue-batch-20260929/engineering907/source03/{stdout,stderr}.log

Cases include original source preparation/ROI roundtrip for .65/.217/converted
nanometers/anisotropic/ZYX calibration, invalid and partial headers, source
publication/manual metadata, absent calibration, relative frame, mixed unknown
and physical sources, conflicting physical sources, and strict scalar rejection.
The unknown case exercises the actual viewer calibrated_metadata consumer and
native-coordinate projection; it is not a live MCP viewer claim.

source01 collection failed on old foreign PolyStore, before tests. source02
origin assertion failed because receiving28 was cold-relocated under HDD; no
product failure. Both logs remain beside source03. Correct source03 resolves
the original target path and uses the existing qualified backing, no overlay.

Installed affected user path
----------------------------

Completed by Singer using the original receiving28 whole-builder/materializer/
verifier and recorded dev_client owner, with a fresh isolated target and one
recorded client. No historical fleet lane or runtime was adopted. See
LIVE-ACCEPTANCE01.rst and the retained original journals in live01.tar.gz.
The saved raw/GraphROI unknown-spacing path and explicit physical raw/ROI
control passed, then both native viewers acknowledged close/process exit and
the client exited0. No detector execution, global install or dependency edit.
