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
