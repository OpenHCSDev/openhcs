Graph ROI native-source roundtrip: receiving 134
===============================================

Status and ownership
--------------------

Singer owns the receiving source test/proposal in draft404. Root owns production
integration in394, including ``openhcs/processing/materialization/core.py``.
The tested proposal is against actual394 head
``82243634ce097d0d1a2d9e77664cbfeac3e6ec94``. Production files in Singer's branch
remain unchanged. Shared writer coordination is visible at
https://github.com/OpenHCSDev/openhcs/pull/394#issuecomment-5945727465.
This is a source checkpoint, not installed/native readiness. Saved-directory
publication is already integrated by Root and is not reimplemented here.

Original receiving witness
--------------------------

Parent retained ``GRAPH-ROI-REOPEN-134-RECEIVING-20261002.rst`` under
``/home/ts/wt/openhcs-issue-batch-20260929``. The candidate6 saved
``A01_s001_w2_z001_t001_neurite_morphology_step0.graph.roi.zip`` resolves through
public result inventory but native reopening refuses missing embedded source
identity. Original request/error remains in the author's actual recorder:
``/home/ts/wt/openhcs-issue-batch-20260929/neurite-development-skill383-20261001/output/assisted-2-post426-1.stdout``.
Read-only verification locates ``plate_file_stream_failed`` at line7602 and the
``ValueError`` message requiring native ROI source metadata at line7605, naming
the exact candidate6 graph ZIP above. This corrects the recorder reference in
the ddbc1b197 receipt; historical receiving receipts and original archives remain
unchanged. The original broken archive was not opened, rewritten or backfilled.

Required relation and original owners
-------------------------------------

An authorised graph archive must preserve its already-declared source identity,
selected channel/plane, declared coordinate spacing, polyline geometry and
neuron subject/edge features through writing and loading. Native reopening must
still reject absent, unbound, partially bound or conflicting source declarations.

``SpatialGraph.contextualized_source_provenance`` owns explicit source-plane
selection. ``SpatialGraphFunctionOutputContextStrategy`` consumes that hook and
attaches invocation provenance before materialisation. It already produces a
scalar selected-source graph, including when the original plane index is1.
Selecting that index again from the scalar graph would be incorrect.

``MaterializationInputItem.metadata`` delegates to ``image_payload_metadata``;
``SpatialGraph`` is not an image-metadata carrier, so that value is empty for
graphs. The original graph carries ``source_provenance`` and
``coordinate_spacing``. The registered graph ROI writer projects those facts
into the existing ``ImagePayloadMetadata`` and ``SourceVoxelSpacing`` owners.
``ROIArchiveSourceMetadata.bind/decode/geometry`` retain the single encoding,
decoding and presentation procedures. ``Output.metadata`` carries the same
declaration into downstream materialisation. No new source schema is introduced.

Exact unapplied proposal
------------------------

``graph-roi-source-roundtrip-134.patch`` contains the narrow production hunk and
one geometry-test adaptation. It uses zero-context Git hunks; integrate with
``git apply --unidiff-zero`` against the named Root source. The production change removes one bare-content
line and adds nine lines in the existing registered leaf writer/imports. The
unchanged binder performs archive encoding. The reader, source-plane projection,
writer registry, subject projection, capture and viewer implementations are
unchanged. Source voxel spacing requires an import from its existing owner;
the first coordination note's statement that core already imported it was
incorrect and is corrected here.

Synthetic Git comparison commit
``3913c5008b606a51268b5aeb4a3c8a527b89f1b0`` has parent82243634c and only the
proposed core file plus the existing geometry-test adaptation. It is a ratchet
comparison object, not an applied production commit or release branch.

``tests/unit/test_graph_roi_source_roundtrip_134.py`` exercises actual context
selection, registered materialisation, disk ZIP writing and original ZIP loading.
It asserts both explicit input planes0/1, exact source/channel/names/provenance,
declared1.3556 spacing, fractional Y/X coordinates, node/edge IDs, graph features,
neuron label and typed subject identity, and transport-field removal from geometry.
The misleading archive filename supplies no identity.

An independent ``AuditedGraph(ProjectionAudit, SpatialGraph)`` declaration
exercises cooperative ``super().__init__`` and before/after
``contextualized_source_provenance`` hooks. Its newly declared
``engineering_confidence`` edge feature survives the same ZIP writer/reader;
no generic consumer or registry changes are needed. This is behavioural MRO
evidence, not an inheritance assertion or ornamental production hierarchy.

The four rejection cases call the original ``StreamingService.stream_rois`` with
``require_source_metadata=True``. They fail before reaching transport; no native
viewer is instantiated. Successful native streaming remains the later parent gate.
The graph type does not declare cropped source-domain bounds. This checkpoint
does not infer or claim such bounds from coordinates or filenames.

Bounded qualification and original failures
-------------------------------------------

Every execution was serial, existing Python/ABI dependencies only, CPU affinity0,
``CPUQuota=100%``, kernel ``MemoryMax=512M``, ``MemorySwapMax=0``, shell deadline60s,
pytest external plugins/cache disabled and numerical thread counts1. Tests use
only explicitly constructed disk storage; a fixture fails optional storage
bootstrap. No native/MCP/UI launch, package/environment change, download, provider,
scientific execution or shared slot was used.

The existing source-selection runner now loads changed OpenHCS Python modules
directly from pinned Git blobs when ``QA134_GIT_REF`` is supplied. Unchanged files
come from the existing branch, equal to that revision; only the proposed core
overrides a blob. This avoids another worktree/full source snapshot and preserves
the actual current dependency closure instead of monkeypatching product methods.

Original logs, including harness failures, are retained in the paired archive:

* ``original.log``: collection fails because a partial current-source selection
  lacked ``DurableSourceMetadata``;1.74s/91656KiB. No product assertion executed.
* ``original2.log``: collection fails because mixing current source metadata with
  old source bindings lacked ``SourceMetadataIdentityProjection``;
  2.22s/79076KiB. No product assertion executed.
* ``pinned-original.log``: exact pinned source, three native-source-loss REDs
  and four rejection controls PASS;2.52s/177464KiB.
* ``proposed.log``: seven receiving cases plus five existing metadata cases,
  12PASS;3.05s/199284KiB.
* ``graph-regression.log``:15PASS/1RED. The existing test compared the bare ROI
  feature mapping including transport metadata. This authentic first failure is
  retained. The proposed adaptation uses original ``geometry`` before the same
  exact feature/coordinate assertions; no assertion is removed or weakened.
* ``graph-regression-final.log``: the existing full graph family,16PASS;
  2.40s/172992KiB. No receiving cases were repeated for ceremony.
* ``r0.log``: original unmodified pinned agent-comms R0 at
  ``3b03785f45df2ef5dc62ba6aed99294192ecbb01``, from the existing
  ``/home/ts/wt/openhcs-s1-original-ratchet-20261001``. Exact822→3913c5008
  comparison includes the entire changed production core file: exit0, every
  delta zero;33.81s/87660KiB. The old UI348 ratchet WT no longer exists;
  no new WT or copied detector was created.

Ownership/antipattern review
----------------------------

Refreshed full NRA skill and authoritative refactor-audit ZIP, catalog README,
boundaries, implementation, membership and surface-receipt guidance were read.
NRA skill SHA256:
``9f2f8b28bc82256eefa3e9d63248c50722dc3ffe7d77adba5793296df196b47e``.
Audit ZIP SHA256:
``ef0367d878cc57565f2b257a8e6647a234d4ba4298f61391709d9c3c82bec9f7``.

BOUND-2/BOUND-8 classify the lost original source declaration at the writer
boundary. IMPL-12 is avoided by reusing the shared binder/decoder/geometry owner
rather than copying metadata encoding. IMPL-3/IMPL-5 and MEMB-1/MEMB-2 introduce
no new consumer type switch, repeated dispatch or roster. The registered writer
is the existing format leaf; shared algorithms remain on their original owners.
No forwarding facade, compatibility reader or parallel store is introduced.
This source review and original R0 pass are not a complete global NRA/R1 scan;
earlier bounded global-scan failures remain in the historical receiving receipts.

Disposition and later acceptance
--------------------------------

Root integrates this tested hunk/test in394 or explicitly releases only that
shared hunk before Singer edits production.404 publishes the receiving test,
patch and evidence rather than another competing writer. Parent controls the
installed freeze release and later public inventory→owned native reopen of a
new correctly written graph ZIP, with source/channel/calibration readbacks and
personally opened same-coordinate raw/result/combined placement. Existing failed
jobs/archives remain unchanged; no biological acceptance is claimed.

Owned scratch is ``.qa134-graph-20261002`` in Singer's existing persistent WT.
Cleanup remains stopped; no completed disposable directories were deleted here.
The byte-exact original logs and synthetic engineering ZIP inputs/outputs are
archived, not reformatted to remove their authentic whitespace.
Archive: ``graph-roi-source-roundtrip-134-source-20261002.tar.gz``; SHA256
``0b04936ffd6f54fb124f4c5ce27f300f72bd83af01922bc874e7e5014efbf375``.
Direct archive reads match the original negative and positive raw-log hashes.
