S1 native summary/sample/ROI and historical receipt closure
==========================================================

Source/integration owner Lorentz, PR413, original S1 issue407. Parent owns
private-wheel integration and installed/native acceptance. This is source-only
qualification: no install, environment mutation, native/viewer launch/control,
scientific job or biological replay. Execution.py and PR394 files are untouched.

Exact coherent source and receiving ownership
---------------------------------------------

Production/test checkpoint1c32652408faf554b3a2970ab3d388325eee03e8 normally
integrates main25d56ae3fb9b80acda80f3cf4e1c8667939147eb through merge
6dfd632ee376013dfb9ef88667bc69f8670bc46a. Parent released original native
runtime/viewer_protocol.py and runtime/napari_viewer_server.py plus original
agent/dto/viewer.py and agent/services/viewer_window_service.py. After the
6b76266 closure census, parent also released historical receipt admission in
agent/services/plate_streaming_service.py (old lines398-412). The fresh394
census excludes this service and parent217/414/418 do not edit it. Receiving
receipt records that release; renderer/viewer.py remains this original S1 owner.

Shared algorithms and independent capabilities
---------------------------------------------

ViewerProjectionRecord extends the original ViewerDeclaredWireValue field
projection. It owns shared annotation validation, declaration-derived boundary
descent, sparse wire projection and cooperative validate_record/wire_overrides
hooks. No separate loader, registry, stored metadata mirror or DTO facade exists.
ViewerPayloadSummary composes aggregate, source-spatial, shape and array
capabilities by actual cooperative MI. Leaves add owned fields and small hooks;
shape bounds reuse the original native geometry result. Missing fields use an
internal absent marker, not JSON null/false/zero/empty; canonical to_jsonable
retains the external JSON containers and sparse values exactly.

NapariViewerProjectionABC owns the existing array/nonzero/shape and sampling
algorithms. Native factories are its minimal payload_summary_type and
payload_record_type hooks. Original coordinate bounds, nonzero limits, sample
slice validation, element budgets and omission reasons are retained. Original
DTOs descend from these actual native records. ViewerWindowService no longer
rebuilds sample dictionaries or rereads native summary maps. Its original ROI
aggregation algorithm consumes contributions through inherited
ViewerPayloadRecord.roi_payload_records and the original service factory hook;
it does not gain a datatype switch or copy the geometry/dedup algorithm.

Historical receipt admission now queries require_plane_components,
full_image_plane_count and source_domain on that original summary authority.
Missing/null domains remain failures, not empty-map fallbacks. The existing
ordered component-domain parser, source-plane provenance expansion, SHA256/URI/
byte-count authentication, producer identity, uncropped-window and transform
checks remain the original mechanisms. Replaced map readers and the unused
spatial-domain parser import are deleted, not retained as compatibility paths.

ViewerResultRenderer owns inherited canonical batch/error/warning framing.
State/payload/sample/ROI presentation consumes original typed records. Native
sample values remain bounded to64 JSON leaves; ROI examples to2; state summaries
to3 and payload records to5. The declaration guard derives renderer membership
and inherited ancestors from the original declaration catalog, not a roster.

Behavioral evidence and current-main crossing
--------------------------------------------

Current-main source tests use the existing readonly parent interpreter at
/home/ts/wt/openhcs-paired-raw-installed-parent-20261001/.venv/bin/python with
this worktree as OPENHCS_SOURCE_TEST_ROOT and PYTHONPATH. source_shard.py borrows
only the existing two extension ABIs and asserts original source modules come
from this worktree. Installed backing dependencies are metaclass-registry0.2.1
and python-introspect0.1.14; these are not a claim of installed current-main
minimum0.2.2 acceptance. Parent owns that next safe integration boundary.

All shards use original run_bounded_source.py, systemd MemoryMax512M,
MemorySwapMax0, CPUQuota100%, outer timeout60s, execution58s plus2s shutdown,
single-thread pool variables and disabled unrelated pytest plugins. Commands,
original logs/XML and resource measurements are retained byte-exact in the
finite archive manifest accompanying this receipt.

* receipt-closure-red:2 failures at the original historical map reader,
  TypeError 'ViewerPayloadSummary' object is not subscriptable.508120KiB/9.425s.
  The fixture's direct summary declaration was first migrated to the original
  native type; no product guard was bypassed to produce or repair this red.
* receipt-native-final:2 passed,516656KiB/10.052s. Actual synthetic native
  projection and aggregate-axis authority create the typed summary; canonical
  state bytes are authenticated and admitted through PlateStreamingService;
  original ViewerStreamingSource reloads persisted TIFF and exact144 pixels.
  Channel order remains2,1 through projection/display ordering. Native int64
  wins even with a deliberately incorrect historical int32 summary; no native
  pixel facts are replaced by receipt metadata. Canonical public MCP batch
  descends back to ViewerPayloadSummary and its original binding renders the
  actual aggregate and source-shape facts. No native application is launched.
* receipt-controls-final:19 passed,258392KiB/5.408s. Original path uniqueness,
  producer/transform/truncation/full-window refusals and declaration-domain
  ordering/conflicts remain. Boolean shape/origin facts now fail earlier with
  TypeError at original typed ingress, not a later ValueError after raw reads.
  Missing/null/empty/ambiguous domains and unowned source refs fail through
  actual receipt service admission; unknown external fields remain rejected.
* receipt-mcp-final:1 passed,302140KiB/7.397s. Original in-process MCP tool
  declaration and dispatch retains source receipt and explicit UI bridge
  arguments; it does not launch or mutate a UI/native process.
* current-main-typed:42 passed,90 deselected,302176KiB/8.139s. Original service
  validation/ROI plus canonical renderer controls cover native post406 camera,
  canvas/contrast/gamma facts, errors, absence/zero/false, exact count validation,
  derived declaration guard and independent presentation capabilities.
* current-main-native:15 passed,517784KiB/10.268s. Complete new synthetic native
  record controls exercise original bounded arrays/omission, ROI semantics,
  typed public presentation and independent audit/ROI capability hooks.

Together these current-main shards complete79 source cases at the coherent
checkpoint. Earlier native-projection-controls retained12 original projection
passes,490636KiB/9.920s, including original state/payload/ROI geometries; those
are prior checkpoint evidence, not a claimed new installed/current-main run.

Independent new-case tests exercise real behavior, not inheritance assertions:
AuditedSummary composes an independent audit capability with native summary
capabilities, executes cooperative validation and wire hooks, preserves native
shape bounds and rejects an empty aggregate domain through the inherited hook.
An independent declared state/capability descends and renders without shared
consumer edits. A separate ROI-family contribution mixin executes super(), adds
ROIS to the unchanged original service algorithm via its existing record factory,
and verifies exact ROI counts, label0 and compact presentation. Original bounded
array crop values, omission/budget0, semantic ROI dedup, geometry/source bounds
and statistics are exercised by native-record controls, not mocked algorithms.

Original R0 and explicit R1 coverage limits
-----------------------------------------

Unmodified packaged R0 SHA256
e323c94d49c2b72d9524a5169f123e64b4a6e46a41035ca9fb4497e49b6ca562.
Exact --root openhcs --base25d56ae3fb9b80acda80f3cf4e1c8667939147eb
--head1c32652408faf554b3a2970ab3d388325eee03e8 covers the complete SIX
changed production paths: agent/dto/viewer.py, both released agent services,
mcp/dev_client_renderers/viewer.py and both native runtime files.5224 original
measurements, no positive delta, exit0;100812KiB aggregate RSS/31.778s/no swap.
This is original changed-path R0, not a whole-repository NRA semantic audit.

Earlier native672 R0 failed with BooleanChainTerms+5 on native protocol and
ForeignAbsenceProbe+1 each on service/renderer. The actual ownership correction
extracted array/domain proof onto those original capabilities, introduced the
native ROI contribution hook and original result-owned empty-ROI permission;
it did not disguise guards or weaken receivers. Native6b R0 passed5216/no
positives before this additional service release; both original reports remain.

Original R1 scripts/check_refactor_r1.py remains byte-identical SHA256
4c6282f52e7c188068dd9d63399f5522a7cb1d222504d0c0b809be10303884ca.
The earlier API-correct full/context attempt used original readonly NRA
673c062fc656e9c74f1eddcab30f036c9befbc1f and original roots/dependency context;
it exhausted58.077s before a completed graph/count/base-head comparison.
STATE-INCREMENT.rst retains exact stderr/monitor/resources. No repeated known
ImportError, detector copying, policy stub, timeout increase, pass or waiver.
No completed R1 comparison is claimed for1c326524. Full-context bounded
preparation remains issue357, not a hidden pass or optional CI hold.

Retained failures and remaining boundaries
------------------------------------------

The first new sampling controls used the wrong test request keyword and then
the wrong inner JSON tuple expectation; both failed receipts are retained, then
corrected to the original request/schema and actual canonical JSON containers.
A full-summary Pydantic TypeAdapter test encountered the existing implicit
recursive JsonObject alias; public descent uses the original dataclass decoder,
not that unsupported codec. Only the actual scalar capability schema is qualified;
its nonserializable internal absent-default warning is retained explicitly.

public-mcp-records-initial retains4 real in-process MCP passes and4 unsupported
old CLI fixture failures: those maps lack mandatory original batch server framing.
No compatibility reader, fabricated server, assertion weakening or raw fallback.
The new canonical batch controls exercise actual current presentation instead.

receipt-closure-green's combined shard hit526384KiB and was terminated by the
unchanged512MiB aggregate monitor; it is not a completed pass. Its receipt/native
rejection also exposed the old synthetic microscope fixture's missing metadata
provider after current main's calibration change. receipt-native-green retains
the exact two AttributeErrors. The fixture now explicitly supplies unknown
spacing through the original provider method; no unit/default calibration is
invented and the original no-spacing assertion remains. Splitting the native,
receipt-control and MCP shards resolves resource overlap without raising bounds.

Both own stashes6d1d1dd255f79db955fa28249f96e5aabaa5b01a and
f16dc72a027427359495eee9a76a4869e0dc44ac remain unchanged. Resource check
warns /home5.1GiB, /7.7GiB and used swap10.4GiB; no parallel heavy work.
Owned scratch/s1_* consists only of disposable synthetic test/cache artifacts.
Durable receipts and original failures are retained. Full S1 navigation/runtime/
snapshot closure remains open; execution.py/394 are not silently absorbed.
Source coherence is not installed/native or biological acceptance. Parent owns
safe closed-slot installation and original live entrypoint qualification.

Finite evidence publication and scratch disposition
--------------------------------------------------

native-records-evidence.tar.gz is430165bytes, SHA256
a65b053280d100f8957d81bfe8c0db0bf64d333b5d2d25df6a2a81eacebb2c48.
NATIVE-RECORDS-ARCHIVE-MEMBERS.txt names exactly68 original generated receipts;
NATIVE-RECORDS-SHA256SUMS authenticates every unmodified member. tar --compare
passed, and a fresh extraction into owned scratch/s1_native_archive_verify
passed all68 member SHA256 checks. NATIVE-RECORDS-SOURCE-SHA256SUMS authenticates
the complete six-path source union; evidence-only publication does not change
their1c326524 production bytes. No tracked evidence/source/science files were
rearchived or deleted. Raw logs/XML are preserved byte-exact rather than edited
to remove original whitespace or warnings. The checked archive is the versioned
evidence carrier; original raw outputs remain protected locally.

After all exact shard processes exited and lsof reported no open scratch files,
removed only the verified extraction and this receipt cohort's declared
s1_receipt_controls_final, s1_receipt_mcp_final, s1_receipt_native_final,
s1_receipt_native_green, s1_receipt_green, s1_receipt_red and s1_pytest_cache
temporary directories. Their original allocated total was5341184bytes, including
4943872bytes of redundant verified extraction. Synthetic fixtures/cache are
reproducible from the retained tests; no durable receipt was removed. Older
s1_public_mcp_initial and empty s1_r1_294 remain preserved, not broadly cleaned.
