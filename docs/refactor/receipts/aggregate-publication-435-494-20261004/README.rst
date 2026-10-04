Four-plane aggregate publication receiving control (#435 / NEW494)
==================================================================

This extends the original ``test_saved_roles_publish_once_per_persisted_occurrence``
writer/materializer control. It uses four real 5 x 7 uint16 TIFF source planes,
Z0..3, CHANNEL1 grouping, variable Z_INDEX and original source spacing
2/.65/.65 micrometers. The existing output contextualizer, RuntimeValue admission,
FunctionOutputIdentity, image materializer, metadata writer and durable workspace
reader own the complete path. No intrinsic Volume domain is forced: the payload
retains its original runtime-plane provenance and two-dimensional spatial domain.
The existing ARTIFACT_NAME whole-file materialization law saves the 4 x 5 x 7
aggregate at ``A01_s001_w1_z000_t001_fixture_image_494.tif``.

Both included JSON files are byte-exact receipts written BEFORE the occurrence
join. ``pre_join_main_flow`` and ``pre_join_artifacts`` use the existing typed
SourceProjectionMetadataSerializer and include complete persisted metadata;
``produced_records`` uses the existing dataclass JSON serializer. Original host
paths remain unchanged. They identify separately retained physical inputs and
outputs; no pixel dataset or large evidence archive is copied into this packet.

Determining RED and corrected owner law
--------------------------------------

On receiving base ``89666e33ea40de4e50a413a456b55926b9043ecf`` (including root
``6f6414eb1``), the corrected aggregate fixture saves the TIFF, then the strict
join raises ``Conflicting metadata for persisted image occurrence``. Both typed
addresses are Z0. The complete persisted image metadata differ in exactly one
field: the artifact's scalar source-component metadata gains ``z_index: "0"``;
the main-flow aggregate has no scalar Z. Both retain all four original Z planes.
This is an observed failure of the receiving fixture. The exact compared pair
from the historical failed #494 execution was never retained, so its differing
field and actual failure cause remain unproved.

The generic source-context owner now prevents a scalar fallback from filling a
coordinate that varies across the payload's actual runtime source planes. Its
existing variation operation returns immediately for zero/one runtime plane;
non-projectable contributors retain their existing scalar fallback semantics.
The publication owner distinguishes proven aggregate source coordinates from
storage filename coordinates. Intrinsic whole images and varying runtime-plane
aggregates use their represented semantic domain; incomplete incidental metadata
on scalar/contributor-only outputs retains the existing filename-address law.
The join compares the actual two semantic addresses, complete persisted metadata
and independent materialization-record scope. It still checks alias, kind,
producer scope and exact destination before accepting a shared occurrence.

An initially broader incomplete-address-to-None attempt failed the two existing
collapsed Mosaic/contributor publication controls (pixel-size aggregation changed
from .5 to 1). This counterevidence is retained in
``/var/tmp/openhcs-publication435-joined-20261004.log``. That route was rejected;
the corrected law leaves those controls unchanged and passing. Earlier fixture
construction errors, the rejected pre-normalization witness, and the intervening
missing-import failure remain in their original private logs. None is substituted
for the corrected determining RED.

Receiving evidence and limits
-----------------------------

The final gate passes 84 controls in 2.19 seconds: the existing function-output
controls and eleven original/extended receiving cases. For the aggregate positive
case, both complete typed metadata/source maps and CHANNEL1/SITE1/TIME1 scopes
agree; both semantic addresses are None. The storage identity keeps Z0 while
semantic component values have no scalar Z. Ordered source Z0..3, four exact
physical source paths, uint16 dtype and original calibration survive metadata
serialization and workspace reopen. Complete saved pixels equal all 140 source
values. The RED and GREEN physical aggregate TIFF SHA256 is identical:
``083537b57bcf28f80bf8abff0f28452a4f0d66c4ed65e6f400cf4a437a1a4d8a``.

Original scalar path/producer/name/kind negatives remain. Aggregate metadata,
stale producer, kind and independent execution-scope conflicts reject. Aggregate
outputs at distinct physical paths retain two separate occurrences with exact
pixels; the existing whole-artifact identity explicitly includes the source ref,
so those distinct occurrences must not be silently deduplicated or rejected as a
single scalar-plane address.

The standard TIFF metadata receiver retains its actual channel-axis/header facts;
this control does not relabel a four-plane runtime stack as intrinsic ZYX Volume.
At that historical stage, this established the writer/materializer boundary
without public execution or fresh MCP receiving. The completed ordinary receiving
section below now covers those consumers. Neither stage establishes old failed-job
replay, native scientific qualification or performance improvement.

Reproduction and retained receipts
---------------------------------

The final command was::

   taskset -c 2 env PYTHONPATH=/var/tmp/openhcs-volume-source-filename-20261004 /home/ts/code/projects/openhcs/.venv/bin/python -m pytest tests/unit/test_derived_role_publication_435.py tests/unit/test_function_outputs.py -q --basetemp=/var/tmp/openhcs-publication435-complete-20261004

Its complete output is retained at
``/var/tmp/openhcs-publication435-complete-20261004.log``. The determining RED log
is ``/var/tmp/openhcs-publication435-aggregate-red5-20261004.log``. Receipt SHA256:

* ``red-prejoin-operands.json``:
  ``84e9ff8f021ab31f891461fa4a3d4c7fe026a2b8cd5d426f7e9fe4ef540ac50e``.
* ``green-prejoin-operands.json``:
  ``b9d3d83aa92c1ccffaef4df7c899ec97c1e41f41a2306dda5da415a168b21de6``.

Follow-up contributor-only Mosaic seam adjudication
--------------------------------------------------

The existing collapsed Mosaic controls do not include a paired saved artifact.
The initial negative parameter in the same receiving fixture used their actual
semantic case: scalar source components omit SITE, two pixel contributors declare SITE1
and SITE2, and the retained physical filename anchors SITE1. Its image is saved
and materialized through the original ImageFile owner, without overriding output
metadata or constructing a replacement projection.

At that initial stage, this did NOT reproduce the hypothesized new address mismatch. The real
materializer's source-context fallback fills SITE1 into artifact metadata, so both
pre-join addresses are SITE1. The main-flow metadata retains no scalar SITE;
complete persisted metadata therefore disagree and the strict guard rejects.
The same fixture was run once against the current integrated source and once
with both affected production owners restored byte-exact from the pre-fix
``89666e33ea40de4e50a413a456b55926b9043ecf``. Both runs pass the expected rejection
control and have the same determining addresses and differing metadata field.
This establishes no new regression on that actual materializer path; it does not
promote the historical contributor scalar-fill behavior as a universal source
law or establish an independently authored Mosaic production journey.

The unchanged logs and complete pre-join witnesses remain respectively under
``/var/tmp/openhcs-publication435-mosaic-base-20261004`` and
``/var/tmp/openhcs-publication435-mosaic-current-20261004`` (matching ``.log``
files alongside them). No production adjustment or normalized-source API expansion
was made at that initial adjudication stage. The subsequent repair below changes
this parameter to require successful publication.

Completed ordinary installed receiving
-------------------------------------

Both bounded public cases now PASS. The final controller imports production
source ``a0bb0f4089a85475e112cea32d60132c1cd94752`` with the actual installed
editable dependencies, including ZMQRuntime
``04d813fe6c93f74166c05847afb1eae158d3c817``. CustomFunctionManager registers the
original producer bytes; PipelineDocumentAuthority renders, saves and reopens
the typed documents. Public MCP compile/execute reaches COMPLETE. Complete public
inventory and pixel samples pass, followed by identical readback in a second
independent SDK process.

The aggregate execution was already COMPLETE on
``ee23a11d4f05e088fc5e267e98862281d993eb29`` and is reused byte-exact without
processing again. All nine inventory records remain visible: four source image
planes, four scalar checkpoints and one named aggregate. The named aggregate
retains all 140 uint16 values in a 4 x 5 x 7 array, 2/.65/.65 micrometer spacing,
ordered runtime Z0..3 and their four original physical contributors. Its semantic
address is None; CHANNEL1 scope fixes SITE1/TIME1 and carries no scalar Z. Exactly
one durable row describes this named physical occurrence. Scalar records remain
in the complete inventory and are not mislabeled as aggregates.

The fresh Mosaic execution on ``a0bb0f408`` consumes two real 4 x 5 TIFFs and
returns a genuine two-dimensional 8 x 5 image through SourceProjectedImageOutput.
All three main/checkpoint/named physical outputs retain all 40 uint16 values,
.5/.5 micrometer spacing, two ordered original SITE1/SITE2 contributors and zero
runtime planes. Scalar SITE and plane axis are absent. Each has semantic address
None and its own single durable row. The producer explicitly drops the source
spatial grid: rank remains two, while source origin and source shape are None.
Output array geometry is independently 8 x 5.

Two remaining generic defects were exposed and fixed through existing owners:

* Workspace REL/FULL keys can refer to the identical SourceProjection.
  SourcePatternResolutionContext now counts that object as one declaration
  position while retaining both identity paths and separately resolved metadata
  records. Distinct projection instances and mapping-only declarations remain
  independent; strict ambiguity and source-position checks stay active.
* FunctionCoreExecutor.save_artifact_outputs already normalizes the selected
  canonical producer value. Removing outer recontextualization prevents consumed
  runtime planes from being restored onto a contributor-only Mosaic. Raw and
  unselected-canonical outputs still contextualize after save callbacks;
  adapter-owned and NoMain branches retain their existing behavior.

The authoritative final receipt is
``/home/ts/.local/state/openhcs-maintenance/20261004/public-435-aggregate-mosaic-v8/journey.json``.
``public-receiving-summary.json`` pins that receipt, controller/helper, source and
environment freeze, all 3 Mosaic / all 9 aggregate physical records, metadata,
prior failure receipts and two direct production-owner replays. The freeze pins
50 prepared files, including original custom functions, six input TIFFs, valid
saved documents, v4-v7 receipts and earlier complete outputs. The earlier v3
receipt is retained separately. Startup-owned registry caches may populate;
scientific inputs, source and installed dependencies are unchanged. Only the fresh
Mosaic output folder is relocated; the recorded AST check preserves the original
pipeline steps and source-binding declaration.

The exact final commands were::

   /home/ts/code/projects/openhcs/.venv/bin/python -B /var/tmp/run_public_435_aggregate_mosaic_qualified_v8_20261004.py --qualify-head a0bb0f4089a85475e112cea32d60132c1cd94752
   /home/ts/code/projects/openhcs/.venv/bin/python -B /var/tmp/run_public_435_aggregate_mosaic_qualified_v8_20261004.py --run

The run used owned port 6563, CPU3, a 600-second journey deadline and a 128 MiB
data guard. Final source/dependency/interpreter/native/input/controller and prior
output guards pass. Controller exit is zero; runtime PID 1285281 (create time
1791103474.58) acknowledges close and exits. Both SDK children exit zero and the
official execution lease is released. Missing plate grid dimensions legitimately
produce PARTIAL inspection with no other warning; no grid is manufactured.

Earlier v3-v7 failures remain unchanged. The v3 fixture omitted filename metadata
extraction, so did not declare its intended Z domain; v4 corrects that declaration
through MetadataExtractionRule without changing input or producer bytes.
Subsequent alias ambiguity and double normalization were real production defects.
Enum/property/checker mistakes and rejected source-grid expectations are retained
separately. No saved output metadata is repaired by hand.

This completes the ordinary synthetic NEW494 aggregate and contributor-only
Mosaic receiving obligation. It does not replay the unavailable historical
biological #494 job or prove that failure cause. It makes no native CP or
performance claim: V15 timings and twelve native comparisons remain separately
qualified on source ``4f2e44701`` and are not rerun or attributed to this
correctness follow-up.


Contributor-only source authority repair
---------------------------------------

The follow-up uses two real physical 4 x 5 uint16 TIFF sources, SITE1 and SITE2,
loaded through FileManager and retained as contributor-only provenance of the
2 x 4 x 5 Mosaic. Scalar semantic metadata omits SITE; its storage filename remains
``A01_s001_w2_z001_t001_MosaicRole.tif``. These parseable physical sources are a
new concrete fixture, distinct from the original unparseable ``site-1.tif`` and
``site-2.tif`` placeholders. The earlier placeholder rejection remains historical
evidence, not a claimed replay of the new physical control.

Restoring the three affected production files byte-exact from ``67aee7cf7``
(root ``2193a86fd`` plus the earlier fixture/docs adjudication) makes the physical
control fail the real persisted-image metadata guard. Both pre-join addresses are
SITE1; the materializer injects SITE1 and an extension into semantic source
identity, while the main-flow payload omits SITE. Complete typed operands and
actual persisted records are retained in ``mosaic-source-owner-red.json``.

The fix removes the storage-to-source identity merge helper. Materialization
reads the existing payload provenance and actual execution scope; storage
basename/filename identity remain independently owned. A source-path-only scalar
is admitted from its ORIGINAL source path before scope attachment, excluding
intrinsic whole images and every runtime-plane/contributor declaration. Shared
numeric component canonicalization now belongs to SourceMetadataFields; output
filename coercion derives from that owner without constructing source-to-output-
to-source identity views. Explicit writer declarations may still select viewer
routing metadata from the filename identity. Those values feed only the declared
writer/viewer selector, never typed Output metadata or persisted provenance.

Main-flow publication derives its address from semantic source metadata. An
incomplete aggregate is an existing SourceArtifactProjection with address None
and actual producer scope. The join still compares exact address, complete image
metadata and actual record scope. Atomic geometry derives calibration through
existing execution_anchor_projections, preserving aggregate-only .5 micrometer
spacing without inventing a scalar plane address.

The corrected physical control has equal complete pre-join metadata, semantic
address None, and identical actual scope on both operands. Durable JSON readback
retains absent scalar SITE, both original contributor paths/sites, zero runtime
source planes, .5/.5 micrometer spacing, and all 40 reopened uint16 pixel values.
``mosaic-source-owner-green.json`` retains the complete operands. Original
scalar/aggregate negative kind, path, source metadata and producer-scope controls
remain active. Real scalar path/alias admissions, ROI storage names and RGB
filename-selector controls remain active as separate contracts.

Final validation of this historical repair is recorded below. Its unit control
does not itself claim public execution, foreign failed-job replay, native
scientific qualification or performance gain. The completed ordinary receiving
section above supplies separate public execution and fresh-reopen evidence.

The final coupled command was::

   taskset -c 3 env PYTHONPATH=/var/tmp/openhcs-volume-source-filename-20261004 /home/ts/code/projects/openhcs/.venv/bin/python -m pytest -q tests/unit/test_function_artifact_materialization.py tests/unit/test_function_outputs.py tests/unit/test_derived_role_publication_435.py tests/unit/test_source_metadata_owner.py tests/unit/test_source_metadata_live_mutation.py --basetemp=/var/tmp/openhcs-publication435-source-owner-final-20261004

Result: 202 PASS in 3.31 seconds. Full log:
``/var/tmp/openhcs-publication435-source-owner-final-20261004.log``.
The real physical baseline RED log is
``/var/tmp/openhcs-publication435-physical-mosaic-red-20261004.log``.
The initial broad attempt's 11 supported scalar/storage/selector failures remain
in ``/var/tmp/openhcs-publication435-source-owner-gate-20261004.log``; they were
corrected through the owners described above, not waived. The later two
canonicalization failures remain in the corresponding ``gate2`` log.

Receipt SHA256:

* ``mosaic-source-owner-red.json``: ``5d5274beffe5dd5346977a5d88e447d1e81051d91c25b123c65c0d1933123e8b``.

* ``mosaic-source-owner-green.json``: ``33bb923dc9351be385843f9d4282398c09996c8571ce3d4a7563227d990a0e15``.
