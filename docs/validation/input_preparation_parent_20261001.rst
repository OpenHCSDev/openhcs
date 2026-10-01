Paired input-preparation parent checkpoint
=========================================

Parent is the integration owner of existing OpenHCS206 / PolyStore16. Original
feature worktrees are unchanged. Published parente0dd14ed3 normally integrates
current main74eac059 as e8d6d32f857254cb84087ad712d1226697afab97. Child50c1e49
normally integrates the application's recorded PolyStoredc341739 as
cb12a2acd91061d60cb6ec65981a9f5c01e18963. Final child4939979978439a6f38145788df9aac3bce65bc70
adds only its canonical receipt to that tested production source. This checkpoint
adopts that final child gitlink; the other seven dependencies remain unchanged.

Actual source validation uses Python3.12 and the existing shared interpreter's
third-party dependencies, not its installed OpenHCS/PolyStore sources. Own exact
external worktrees are populated from existing local Git objects; no package,
interpreter, Fiji bundle or JVM download occurs. Source-built native extensions
are produced by the standard setup.py build_ext --inplace in this own tree.
No shared or frozen installation is changed.

Forty-eight dependency tests pass in0.82s: existing ROI, new RegionProperties
geometry/work-count and actual Java-context lifetime owners with controlled
external responses. The dependency process verifies its source location and
generic polystore_metadata.json configuration before collection.

One hundred sixty-three application tests pass in19.12s: source-binding
workspace, source-plane stores, BioFormats handler/adapter/storage/SPW/validation,
physical preparation/admission, fragmented materialization and both synthetic
generator families. The fresh process imports the real openhcs entrypoint before
pytest, verifies both source paths and openhcs_metadata.json configuration,
and uses no plugin autoload or global conftests. Two unrelated asyncio config
warnings arise because those optional plugins are disabled. No assertion,
metadata filename or application/dependency API is patched for these checks.

Historical141-pass/26-failure output remains historical. An intentional fresh
dependency-first control reproduces the current failure: the normalized-workspace
test writes the application metadata but VirtualWorkspaceBackend._load_mapping
looks for the earlier-decoded generic filename. Actual result1 failed in3.34s;
this is not a green test or a repaired embedding contract. Issue327 tracks the
actual reproducer and parent owner. The first control's
missing pytest scratch parent yields1 setup error in3.17s and is retained as a
separate harness mistake, not evidence of the product defect. Parent owns the
namespace-boundary follow-up; no singleton mutation or second filename reader is
introduced here. These separately bootstrapped passes establish current source
preservation, not global elimination of the import-order defect.

Existing bounded128x128 ROI profile now runs: original parent labels7/42/188,
fragment counts1/1/900,902 native ZIP members, one find_objects scan. Earlier
same-fixture profile recorded two scans. Current cold extraction0.284355s,
warm profiled extraction0.019384s, separate member conversion0.060257s,
archive conversion/write0.133487s. A single-fixture work-count reduction is
observed; no general speedup or biological quality claim is made. Polygon rings
still do not declare hole subtraction; archive reopen is not raster/viewer
equivalence. Exact label TIFF and full-mask controls remain distinct.

BOUND-2 / IMPL-13: existing RegionProperties and BioFormatsJavaContext own
crop/reader lifetime; existing NamedSourceBinding/SourceSelector own physical
admission. Consumers reuse those nominal operations. No decoder/filename roster,
alternate extractor, mirrored provenance/configuration or type/name switch is
added by this integration. Earlier focused ownership guards remain covered by
the current211 source checks. Full NRA/R1 and the owner's complete ZIP scope are
not certified. Installed stdio/native preparation, actual Java/CZI and new
generation/inspect/sample acceptance remain separate next-slot requirements.

Raw source receipts, XMLs, profile and original negative-control errors remain
at /home/ts/wt/openhcs-issue-batch-20260929/input-parent-20261001. All source shards
have an unchanged60-second shell bound and one numerical thread. Disposable build,
pytest and profile output is tracked under the parent's named input-parent-20261001
scratch directory. Active independent H003f's source, skills, runtime handles,
scientific inputs/settings and protected user viewers are untouched. Neither
issue132 nor172 is closed by this source-only checkpoint.
