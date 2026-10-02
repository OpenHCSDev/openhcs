ROI-only publication: exact original-owner hook proposal
=======================================================

Current disposition, 2026-10-02: the source publication requirement is integrated
by Root in PR394 at ``82243634ce097d0d1a2d9e77664cbfeac3e6ec94`` and accepted
by Singer's receiving diff/receipt review. The source seam is no longer awaiting
an owner or release. Root owns integration; draft404 remains the receiving
evidence/native-acceptance record, not another production implementation to merge.
Committed PR source is distinct from merged, installed and native acceptance.
The exact review and remaining parent gate appear in the final section.

Root integrated the distinct graph source-metadata writer repair in394 at45f3a721e.
Singer resumes404 receiving ownership under Tristan's latest explicit correction;
the verified source checkpoint and parent-owned installed/native gate are in
``graph-roi-source-roundtrip-134.rst``. The publication proposal below is still
superseded and must not be reapplied.

The historical proposal below was qualified against PR394
``faf61ad87c550fa2d8ef44313344db74b378b857`` before Root's integration.
Original public reproducer, failed controls and completed image scope remain in
``persisted-roi-admission-134.rst``. No shared source or foreign worktree was edited.

Required relation and exact owners
----------------------------------

Every successfully saved artifact destination can publish its existing
result-directory identity even when no image was saved. A declared result
directory is not an image source address or an ROI provenance receipt. The shared
transaction must preserve strict image-address validation while publishing
non-image results without constructing an invalid empty image set.

The historical combined delta is ``persisted-roi-only-owner-134.patch``;
it superseded the three-hunk proposal, and is now superseded by Root's integrated
implementation. Do not apply either archived proposal over PR394. Admission against selected
original PR394 files passes with ``git apply --check --unidiff-zero`` and the
explicit projection directory. It changes only ``core/steps/function_outputs.py``
(17 lines removed, 41 added) and ``core/virtual_workspace_metadata.py``
(6 removed, 7 added). Paths are relative to ``openhcs``.

* Original ``MaterializationBatch.save`` and
  ``SavedMaterializationOutputs.outputs_for_backend`` remain unchanged. Their
  successfully saved outputs, not predicted filenames or another render, select
  runtime destination directories. The image-only selection predicate is deleted.
* Existing ``OutputTarget`` owns guarded publication participation through
  ``contains_outputs`` and the minimal ``stored_output_paths`` hook. The replaced
  ``contains_images`` method/calls are removed, not retained as aliases. Image
  declarations keep their original image-only path hook.
* ``PersistedResultMetadataCapability`` composes cooperatively with that ancestor
  on ``RuntimeArtifactMetadataTarget``. Its ``super().stored_output_paths`` keeps
  image participation and includes actual files in the declared saved-result
  destination. No extension roster or format switch is added: existing
  ``PlateResultFileInventory`` remains the sole format-classification owner.
* Existing runtime destination hooks keep the exact plate-relative results
  identity from the first proposal. After runtime values are released, the leaf
  calls original ``OpenHCSMetadataHandler.analysis_result_directories`` to obtain
  already-declared destinations alongside retained image projections. It does
  not decode another results store or fabricate a historical viewer receipt.
* Existing ``AtomicMetadataWriter.publish_source_projection_metadata`` remains
  the single transaction. It calls image-set/component projection only when saved
  addressed images exist. Missing-image-address rejection, concurrent-step
  publication, final pruning and geometry reuse remain intact.
  ``SourceProjectionSet`` itself keeps its strict non-empty invariant.

Catalog review: MEMB-2 identifies image participation mistaken for the entire
saved-result capability; BOUND-2/BOUND-8 require the original saved-outcome and
directory owners across publication; IMPL-12 excludes a second writer or render.
The new nominal hook changes the relation, rather than forwarding a relocated
algorithm. No source-binding/component-axis, capture, renderer, function-registry,
startup, installed-package or scientific-processing change is proposed. Diataxis
reference structure separates exact owners and evidence from remaining acceptance.

Five additional source cases and new declaration
------------------------------------------------

``tests/unit/test_persisted_roi_only_publication.py`` selects original typed
PR394 batch/outcome/target owners through
``docs/validation/check-persisted-roi-only-proposal-134.py``. Seven exact source
files close original imports; only the two proposed owners differ. The existing
receiving runner owns ABI preparation and pytest invocation. This is an explicit
selected-source qualification, not an installed package or ordinary main-tree
test pass. Source blobs and selection are retained in the archive.

The real declared ``FileBundleOptions`` writer and disk backend save synthetic
archive-admission bytes once. Input mutation plus a test refusal hook proves
publication cannot render that batch again. No actual ROI geometry or pixel
processing is performed. Simple and unrelated nested ROI-only destinations pass
through original registry discovery, shared step publication, public typed
``query_files(kind=result, include_previews=false)`` and completed-plate
reconciliation after saved outcomes are gone.

An independent ``IndependentSavedResultMetadataTarget`` supplies only its own
destination declaration. Its declared MRO composes publication audit, existing
``ProducedImageMetadataCapability``, runtime result capability and original
``OutputTarget``. Cooperative before/after write hooks and real original record
and storage hooks execute; public inventory admits the exact synthetic ROI.
No generic consumer or registry roster edit is required for the new case.
Additional controls preserve refusal of an unaddressed saved image with the
metadata document byte-exact unchanged, and prove filesystem artefacts without
successful batch outcomes cannot create step publication targets.

Original PR394 control: 4 failures / 1 pass, 5.55s elapsed, 235884 KiB maximum
process RSS. ROI-only targets are omitted, direct publication rejects the empty
image set, and the new declaration cannot participate. Final proposed source:
5 passes, 4.50s elapsed, 236380 KiB. All source checks are serial one-CPU,
kernel512MiB/no-swap/60s/provider-free/plugin-free, distinct from parent native
and biological acceptance. Existing first-proposal five passes were not rerun as
a ceremony. Global NRA/R1 completion is not asserted.

Retained corrections and resource incident
------------------------------------------

The initial five-file selection failed collection because an original main
worker imported a function removed by PR394. Selecting PR394's two original
orchestrator import owners closed that boundary; no compatibility alias was
added. The first projected suite then hit the unchanged 60s limit, exit124,
304412 KiB process RSS. Its default public-service file-manager factory invoked
``ensure_storage_registry`` and created an optional ImageJ bootstrap cache.
That attempted download was unintended and violates the requested download-free
tier; it is not relabelled as a passing source check. No native viewer startup,
installed package edit or parent endpoint mutation occurred.

The receiving fixture now injects the real already-created disk-only manager
through the service's original factory boundary, uses the declared OpenHCS
metadata handler, and fails if optional backend bootstrap is attempted. The next
2-failure/3-pass log is retained: its compiled fixture had left
``create_openhcs_metadata=False``, so the existing default-off contract correctly
did not publish. Enabling the explicitly requested compiled publication contract
produced the final five passes without changing assertions or the product guard.

The bootstrap failure archive is byte-exact and excludes dependency cache bytes:
``persisted-roi-only-bootstrap-failure-134-source-20261001.tar.gz``, SHA256
``cb1aa2043cd32c333dcb0144d0d2396482e596bd98fcbae5d04c6b3120151cb5``.
After archive comparison and exact source-process termination, only
``/home/ts/wt/openhcs-knowledge-lazy-conversion-20261001/.qa134-roi-only-20261001/cache/polystore/imagej``
was removed: 1508931494 logical bytes, reported 1.5GiB. The incomplete dependency
ZIP/extraction are disposable, not scientific or unknown-input data. Original
timeout, input, size evidence and selected code remain retained.

Combined exact original R0 and archive
--------------------------------------

The same unmodified pinned R0 owner qualified the entire two-file proposed delta
against PR394 ``faf61ad87c550fa2d8ef44313344db74b378b857``. Original guard owner:
``/home/ts/wt/comms-ratchet-pinned-ui348-20261001`` at
``3b03785f45df2ef5dc62ba6aed99294192ecbb01``. Command uses Python3.14 and
``python -m agent_comms.debt_ratchet --root openhcs --base faf61ad87c550fa2d8ef44313344db74b378b857 --head e960fe80e396e1c43447aa9990e133c985f22b3d``.

Synthetic proposed commit ``e960fe80e396e1c43447aa9990e133c985f22b3d``, tree
``8ab6dc59fe9c23122cbdea3f35da2de0c2e474ad``; no live ref or working index was
changed. Proposed source blobs are ``d44e511e9711cde0b1c8d3fad93b00d8ddad7de4``
and ``63ce7c84ff2b7807d00d09e5b93168caf94e2050`` respectively.
R0 exit0: every delta zero, both changed production files included, 18.46s,
87772 KiB maximum process RSS, same kernel512MiB/one-CPU/60s bounds. No detector
copy, omitted changed file, increased threshold or waived positive delta.

Final byte-exact archive
``persisted-roi-only-owner-134-source-20261001.tar.gz`` retains all raw logs,
input versions, synthetic failed fixtures, original/proposed selected source,
alternate index and complete R0. SHA256
``0d3c6c02e153f8ad35acccf9f07de0808a585379739658757fe4f22d258ffbbd``.
``tar -d`` passes before release of the remaining owned projection/cache root:
``/home/ts/wt/openhcs-knowledge-lazy-conversion-20261001/.qa134-roi-only-20261001``,
3048192 logical bytes, 3.5MiB filesystem usage. Original evidence is recoverable;
source, durable history, Dalton outputs and all foreign worktrees remain intact.

The former shared-owner wait is resolved by Root's integration below. Public
native ROI reopen/provenance acceptance remains outstanding. Saved image acceptance399,
closed398 scope, snapshot writer/binding ownership, parent viewer guides,
Schrodinger376 and Dewey379 remain untouched. No biological pass is inferred.

Receiving acceptance of Root's integrated source checkpoint
----------------------------------------------------------

Read-only review inspected the exact commit diff, its full new behavioral test,
the PR394 ownership statement and
https://github.com/OpenHCSDev/openhcs/blob/82243634ce097d0d1a2d9e77664cbfeac3e6ec94/docs/validation/persisted_result_publication_134_20261002.rst.
Commit parent is ``4afd5141554299680fa0326b31334a448fbf20bf``. Actual production
delta: ``core/steps/function_outputs.py`` removes16/adds36 lines;
``core/virtual_workspace_metadata.py`` removes6/adds7. No source edit, native
operation, installation, test replay or cleanup was performed for this review.

The integrated relation meets the original receiving requirements:

* Existing ``OutputTarget`` owns guarded ``contains_outputs`` and the
  ``stored_output_paths`` hook. Existing ``RuntimeArtifactMetadataTarget`` supplies
  its minimal all-saved-format hook. Root correctly omitted the proposed separate
  capability class: this production behavior has one existing leaf owner; no
  independent overlapping capability needs another class or duplicate listing.
* Actual saved ``MaterializationBatch`` outcomes select destinations, without
  re-rendering. Generic finalization calls the nominal participation contract.
  The image-only predicate and replaced method disappear; no compatibility alias,
  consumer switch, result roster or parallel authority is added.
* Exact nested results identities and original metadata-handler reconciliation
  survive runtime-value release. The original atomic publisher avoids an empty
  image-set construction while retaining actual unaddressed-image rejection.
  Empty raster inventory does not become a fabricated image source projection.
* Root ported the five receiving behavior cases. The independent declaration
  composes audit, original produced-image capability and runtime target through
  cooperative ``super().write``. Its own ``declaration_key=None`` obtains a new
  derived registry key; complete registry restoration fixes the original test's
  inherited-key contamination rather than weakening later consumers. Public
  admission and before/after hooks are exercised, not inheritance assertions.
  The NumPy-only control now expects a declared result directory with no raster
  records; mixed raster pixel equality remains asserted.

Root's retained receipt reports original four failures/one pass and89 passing
publication/checkpoint/metadata/journey controls on the integrated source. PR394
reports isolated original R0 roots and R1 passing against its ``4afd51415`` parent.
These are Root's execution receipts, not new receiving runs or a global/native
acceptance claim. Original test-path, registry-contamination and source failures
remain retained by Root. Catalog checks MEMB-2, BOUND-2/BOUND-8 and IMPL-12 support
the accepted owner placement; no run-obstructing ownership violation was found in
this two-owner delta. No unrelated architecture audit is requested.

Draft404 disposition and remaining parent native gate
----------------------------------------------------

Production implementation is superseded by PR394 under Root. Do not merge404's
historical patch/test copies over the registry-safe integrated implementation.
Keep404 draft as the receiving evidence and narrowly pending native-acceptance
record while134 remains open. Original failures and archives remain unchanged.
Close or consolidate the draft with Root after the parent records the installed
gate; source integration itself is not waiting on that later gate.

After current freezes end, parent owns the authorised installed entrypoint check:

* Pin an installed source including the accepted publication checkpoint and its
  explicit owned MCP/native endpoint. Use a newly authorised correctly published
  saved-result checkpoint. Ordinary public ``kind=result`` inventory must admit
  the exact ROI archive from durable declared metadata, without an explicit-path
  bypass, fabricated source receipt or silent backfill of the older candidate.
* Reopen that exact materialised archive through the original public viewer route.
  The actual native ROI decoder/source-metadata boundary must accept its existing
  source provenance, selected source channel, plane/spatial domain and calibration.
  Preserve strict rejection if those facts are absent; directory admission alone
  does not repair or prove that separate ROI/graph source contract.
* Retain the original request/reply, native readback and same-coordinate source/
  ROI placement evidence. Distinguish real archive geometry/reopen from synthetic
  filename admission. Preserve old failed jobs without replay and keep rejected
  biological candidates rejected; no segmentation quality or biological pass is
  inferred from an engineering reopen.

This names the remaining acceptance boundary, not authority to modify the frozen
environment, generate another scientific run or claim the broader graph134 fixed.
