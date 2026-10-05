Typed centroid and multi-image authoring checkpoint
==================================================

Owner and scope
---------------

Singer owns this documentation-only change. Planck explicitly released the
callable-artifact authoring and custom-function reference documentation; Planck
retains #748 geometry and its frozen engineering fixtures. No production,
installed package, live author, or scientific input is changed here.

The canonical owner is ``docs/source/development/callable_artifact_authoring.rst``.
The custom-function skill reference routes to that manifest-declared document;
``build_mcp_knowledge_assets.py`` copies both declared sources into package output.
It does not convert this RST into a second Markdown artifact manual.

Determining source contracts
----------------------------

``PointROIOptions`` in ``processing/materialization/options.py`` selects nominal
runtime measurement features. The registered ``_write_point_roi_zip`` writer in
``processing/materialization/core.py`` requires a contextualized measurement
table, object subject, owned coordinate fields, and exact source provenance.
It retains fractional Z through ``ROIFractionalZ`` and binds the archive through
``ROIArchiveSourceMetadata``. There is no new Points artifact declaration.

The read-only engineering494 ``point_volume_fixture_494.py`` is pinned at SHA256
``c883251abc009e9d2c7b82a3dde3b4fe4a66529b6c8117b6bf1bfd887fdc2935``.
Its typed feature owner, subject relation, and CSV plus PointROIOptions supply
the existing declaration example, not an assay algorithm or recommended settings.

``CallableContract.__post_init__`` separates consecutive main-flow Image specs
into canonical return specs; ``resolve_returned_output`` expects those images
in one named ``AlignedImageStack`` return slot. Each remaining typed artifact
has one trailing slot. A flat tuple of diagnostic Images is not this ABI.
``pack_aligned_image_outputs`` and ``AlignedImageSliceContext`` own its packing.

Review and readiness
--------------------

Read current skill-creator, NRA, authoritative refactor-audit archive, pattern
README and boundary patterns, Diataxis and use-openhcs. Relevant BOUND-2/4/8
risks are hand-decoding rows, flattening nominal output families, and inventing
an image/CSV substitute for the materialization contract. Existing owners remain
unchanged; this is not a structural refactor or global NRA proof.

Source reflection, executable declaration/ABI checks and real knowledge/package
projection follow the coherent documentation edit. Native #748 geometry/reopen
qualification remains with Planck/Dewey and is not claimed by these source checks.

Implemented owner/consumer change
--------------------------------

The RST adds one declaration-only centre row/feature owner and measurement output
with CSV plus PointROIOptions; detection is deliberately left to the existing
analysis callable. The original engineering fixture is not edited or copied as
a new detector. The named subject binds the exact labels declaration. The generic
writer accepts this independently named CentreRow/CentreFeatureOwner declaration
without consumer edits, retaining fractional geometry, row features and the full
four-plane source domain. Missing source/field, duplicate-ID and empty-archive
guards remain unchanged. No Points artifact, schema mirror or custom codec is added.

The existing executable image/labels/rows reference gains a diagnostic variant
using the original aligned image packer and named slice-context owner. Its two
Images share one canonical slot and labels/rows retain two trailing slots; the
original matcher rejects the flattened return. Five canonical Images plus three
trailing typed artifacts likewise means four outer return positions, not eight.
This identifies the reported return-count error as an ABI mismatch, not evidence
that diagnostics are unavailable or that a viewer geometry guard must change.

One obsolete direct-check consumer of the deleted RuntimeReturnedOutputMatcher
is migrated to CallableContract.resolve_returned_output. One stale fixture cache
clearing call is deleted: resolved_callable_type_hints now owns fresh resolution,
not that removed cache. No compatibility facade or alternative matcher is added.
Two pre-existing short RST heading underlines are corrected so the existing
knowledge section parser ends each section at its actual boundary. The packaged
custom-function reference links these two sections once, with no duplicated ABI
example or new SKILL entrypoint. Manifest discovery metadata names this same
canonical document; the original package builder copies its exact bytes.

Actual qualification and preserved failures
------------------------------------------

All controls use the existing run_installed_tests.py entrypoint, paired interpreter
and read-only qualified receiving14 runtime/dependencies. Six declaration/source
owners (artifacts, callable contract, runtime measurements, aligned image payload,
options and tabular CPP) byte-match current main. The backing writer includes
unmerged #748 PointROIOutput; native streaming/reopen is explicitly NOT inferred
from this disk/source contract proof. No install/build/catalogue/native/viewer or
provider request occurs. Current live authors and their instructions are untouched.

Original controls01:13PASS/3FAIL,7.02s,377724KiB max RSS, swaps0. Failures were
the new fixture assuming .csv instead of CsvOptions' declared _details.csv,
the pre-existing removed cache API call, and an undersized new RST heading.
Original controls02:15PASS/1FAIL,7.11s,372296KiB max RSS, swaps0. All executable
ABI/materialization tests passed; section retrieval still included later content
because the pre-existing input/plate section underlines were too short.
Final affected controls03:3PASS,6.42s,364996KiB max RSS, swaps0. No larger bound,
parser patch or assertion weakening: correct canonical section boundaries now
retrieve both sections untruncated at10000chars; whole-document retrieval remains
untruncated at30000chars. All16 distinct original controls are qualified by02/03;
this is not reported as a single clean16-test final run.

Real KnowledgeBaseService retrieval/search, exact RST/skill package projection,
isolated managed-skill sync and unchanged second sync pass. The original
skill-creator quick validator reports ``Skill is valid!``. No production changes,
scientific inputs/reference answers, settings recommendations, source calibration
invention or current-author coaching. git diff --check passes on this change;
eight unrelated foreign gitlinks and prior untracked evidence remain untouched.

Raw numbered stdout/stderr and original generated centroid CSV/ROI archive are
preserved in the byte-exact qualification archive adjacent to this receipt.
Its15members compare byte-exact to source; archive SHA256 is
``9cc10ec8c226b8c4d79c599aa6d2f670de7de8ca7432d828c501914cc451c6c9``.
CI is deferred. Documentation/contract exposure is ready for review and future
ordinary package delivery; #748's native geometry/selected-source acceptance
remains the explicit independent scope boundary, not a documentation delivery hold.
