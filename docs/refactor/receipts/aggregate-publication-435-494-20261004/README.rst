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
It establishes the requested writer/materializer publication boundary, not a
public PURE_3D producer execution, old failed-job replay, fresh MCP receiving
journey, native scientific qualification or performance improvement. Ordinary
installed aggregate receiving remains a separate pending acceptance gate.

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

Pending ordinary installed aggregate receiving plan
--------------------------------------------------

Use the existing installed-consumer #419 controller's private output/environment
and public MCP SDK lifecycle, with a NEW synthetic case rather than the failed
#494 job. Freeze the parent-reviewed source/dependency/input epoch before running.
Persist a uniquely named custom function through CustomFunctionManager in its
private XDG data root so parent/server/spawn resolve the same declared source.
The function uses the original public PURE_3D and image-artifact declaration APIs
and copies its input as one named image. Do not force an intrinsic Volume domain.

Write four real 5 x 7 uint16 source TIFFs with complete CHANNEL1/SITE1/WELL A01/
TIME1/Z0..3 identities and 2/.65/.65 micrometer spacing. Author one CHANNEL-grouped,
variable-Z processing step with named source binding, runtime-artifact
materialization and ordinary saved image metadata enabled. Render/save/reopen the
pipeline through PipelineDocumentAuthority. Through the existing fresh MCP SDK
controller, create the session, submit public compile and execute to terminal,
and retain OUTCOMES using the existing export owner.

Inspect/sample the resulting plate in a distinct fresh SDK context. Compare the
complete physical aggregate array against all 140 input values, uint16 and source
calibration; decode the actual durable projection and require one logical saved
occurrence, semantic address None, exact producer scope and all four correlated
source paths/Z coordinates. Record the physical storage filename independently
of that semantic domain. A missing plate grid may legitimately report PARTIAL;
compile/execute and exact source/pixel acceptance must still pass. Shut down only
owned children. This is a plan only: no server, registry, public job or native
client has been launched for this new case.


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

Final validation is recorded below. No installed/public producer execution,
foreign failed-job replay, native scientific qualification, or performance gain
is claimed by this repair. The ordinary installed aggregate receiving plan above
remains pending.

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
