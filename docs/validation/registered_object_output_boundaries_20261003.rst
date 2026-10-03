Registered object-output boundary investigation
==============================================

Scope and source pins
---------------------

Singer: source-only investigation and declaration-side receiving checkpoint.
Root: PR394 shared runtime/label construction/materialization integration owner.
No production patch, runtime retry or installed correctness claim is made.

Tracked receiving defects: #501 (categorical-label/compact-row association),
#502 (FilterObjects optional return ABI). Root's #394 owns shared integration;
Singer owns this receiving trace and #502's declaration-side investigation.

Frozen installed source: 6ce527a29c421ef5a95217b58e8bc33a93ba5fa2, byte-equivalent
to the original package's be6e90cf normal merge. Main audited:
72ae6bf2dd3ddc990c282eb2be200dab717cbd05. Root394 audited:
2d3d75e80309472f6b6b26af067da6e69aa32ab6. The original failed pipeline and
server journal stay at their original locations, referenced only by the local
receiving receipt. No acquisition pixels, heldout/reference answers or science
outputs were decoded; no author was contacted.

The released existing checkout was reused on an ordinary new branch. Merged
PR498's b710ce4 branch/checkpoints and foreign untracked ledgers are preserved.
Its production and packaged-skill bytes equal current72ae main. Dewey was given
the current pin and read-only source clearance for the independently authorized
future package; this investigation does not build or install that package.

Declaration, dimension and source relationships
----------------------------------------------

* ``watershed_library`` and ``watershed_cellprofiler4`` declare PURE_2D processing
  plus an explicit FULL_STACK image execution mode. The latter takes precedence
  in the CellProfiler module invocation. Their request computes on the supplied
  whole image array and creates payload-wide object IDs through the original
  ``SourceImageObjectLabelBuildRequest``.
* That constructor does NOT infer plane-local object IDs from acquisition
  provenance. Without an explicit object-domain projection it creates PAYLOAD
  labels with no object plane axis. This is deliberate, as recorded by #428:
  storage/source planes must not split global volume IDs.
* ``convert_objects_to_image`` declares PURE_3D plus FULL_STACK label input.
  Its existing ImageModeRenderer UINT16 leaf preserves categorical values and
  label provenance; it does not turn volume labels into plane-local objects.
* ``ImageArtifactType.compose_runtime_values`` and compiled runtime artifact
  input selection own grouped image composition; ``ImagePayloadMetadata`` and
  ``RuntimePlaneAxisValueProjection`` own the declared leading image axis.
  The existing registered PURE_2D slicer removes that declared leading axis,
  not arbitrary singleton dimensions or inferred volume axes.
* ``convert_image_to_objects`` declares PURE_2D and calls the region-properties
  owner's ``measure_2d`` after converting the image to labels. Both existing
  NumPy region-property providers deliberately reject labels whose rank is not
  two. No provider swap, squeeze or changed dimensionality guard is justified.

Retained conversion failure
---------------------------

The original registered chain reaches ``execute_pure_2d_slice`` and then fails
inside ``convert_image_to_objects`` with::

    Numba label-region properties currently support 2-D labels.

This establishes higher-rank labels at that original leaf. The trace does not
print the complete intermediate image metadata/shape; no exact extra-axis count
is invented. The controlling question for Root is which source/compiled
projection admits the rendered whole-object payload as a PURE_2D image slice.
The first prospective control is the same registered chain on declared synthetic
2-D source planes, retaining identities/domain/projection at each existing owner;
genuine volume objects and explicit plane-ID domains must remain separate.
If the resulting input is intentionally a volume, rejection by measure_2d is a
declared limitation, not evidence that its backend should accept volume data.
Whether the original route should have projected a plane earlier remains open.

#482 is already merged in the frozen source. It concerns singleton label kwargs
after MATCH_IMAGE_STACK resolves a scalar NATURAL image, not this PURE_2D main
image conversion. Root's current object_images delta changes the image annotation
to RuntimeArrayData, not the conversion algorithm or processing declaration.
Root changes surrounding callable/metadata/context machinery, so this checkpoint
does not equate an unchanged leaf with an installed proof of the whole route.

Independent saved-label / measurement identity witness
------------------------------------------------------

A later, terminal frozen attempt completed through a DIFFERENT producer:
``count_cells_single_channel`` using its existing watershed detection member,
then registered MeasureObjectSizeShape and UINT16 ConvertObjectsToImage.
The retained public categorical-sample / CSV comparison reports unequal ID
sets despite equal cardinalities and unique table keys. No image was decoded
in this investigation. Counts alone cannot qualify categorical correspondence.

The source trace distinguishes producer IDs from exported row identity:

* ``_detect_cells_watershed`` retains surviving original region labels when
  filtering by area. ``_create_segmentation_visualization`` casts that existing
  label array to UINT16; it does not renumber it.
* ``DenseArrayObjectLabelOutputValueContextStrategy`` passes the array and
  declared source projection to ``SourceImageObjectLabelBuildRequest``. Its
  ``PresentObjectLabelIdsDomainDeclaration`` derives material IDs, either for
  the payload or explicitly selected plane domains. No consecutive count-based
  ID declaration is inserted on this producer route.
* ``DenseObjectSizeShapeMeasurement`` / ``ObjectSizeShapeFeatureMeasurement``
  construct raw geometry vectors and row domains. Two-dimensional raw vectors
  use the positive label extent; volume feature rows can use compact ordinals.
  ``ShapeObjectMeasurementRows`` explicitly declares ROW_SEQUENCE, as does
  ``MeasureObjectSizeShapeModule``. That explicit row declaration takes priority
  in ``CellProfilerObjectMeasurementRowPolicy.object_identity_for_rows``.
* The module's genuine existing capability MRO is LabelsObjectInputPolicy,
  CurrentPayloadMeasurementRecordMixin, DenseColumnarObjectMeasurementRowsMixin,
  DeclaredDomainCompactMeasuredObjectMeasurementRowPolicy,
  PerObjectMeasurementExecutionModule, ObjectMeasurementInputModule and feature
  authorities. The dense shortcut only admits covered LABEL_ID rows. The
  declared-domain compact policy's special projection handles ROW_ORDINAL;
  ROW_SEQUENCE delegates through cooperative ``super()`` to the ancestor.
* ``RowSequenceMeasurementObjectRowIdentityProjectionStrategy`` then replaces
  the object-ID column with compact one-based row ordinals. Its shared
  ``CompactMeasurementObjectIdProjectionMixin`` also derives required IDs from
  domain cardinality. This is a declared ordinal policy, not an accidental CSV
  sort or UINT16 overflow. Existing source tests deliberately exercise it.
* Recording completes those rows before constructing the measurement table.
  ``MeasurementFeatureValueIndex`` subsequently keys feature values by the
  table subject's object-ID column. The ColumnarRows CSV projection writes row
  mappings without translating those keys back to the source categorical IDs.
  UINT16 rendering of the label payload independently preserves those IDs.

Therefore the concrete missing relation is between compact measurement row
identity and the original categorical object domain, not an invalid sparse-ID
producer declaration. Neither equality of counts nor a local export renumbering
repairs this relation. Preserve legitimate CellProfiler ordinal semantics while
making the existing object-domain/row-projection owners carry an unambiguous
association through feature lookup and persisted table/label consumers.
Do not globally replace every ROW_SEQUENCE declaration with LABEL_ID, infer
object identity from pixel rank, or change scientific detector settings.

Acceptance must exercise the registered CPU producer -> original typed label
domain -> shape table -> UINT16 image -> physical public inventory/sample path
on synthetic nonconsecutive IDs, with distinct known geometry per object.
Verify each ID-to-feature association, missing-ID behavior, plane-local repeated
IDs and genuine volume domains; consecutive IDs, empty labels and existing
CellProfiler ordinal output contracts must remain valid. A new producer/case
must need only its declaration/hooks, not consumer names or another ID registry.
These behavioral and installed controls have NOT been run here.

Root remains the shared runtime integration owner. Singer supplies this focused
source receiving witness and acceptance dependency, not a competing runtime
patch. The original scientific rejection and all frozen outputs remain intact.

Earlier measurement failures
----------------------------

The original journal records MeasureBeforeFilter execution and finalization
completion before FilterObjects reports absent ``AreaShape_Area``. Physical
result-path inventory contains no MeasureBeforeFilter CSV in the inspected
earlier attempts. These are distinct observations, not proof that no runtime
measurement table was produced.

``MeasureObjectSizeShapeModule`` declares dimension-specific fields. Dense
PAYLOAD volume labels produce ``Volume`` rather than two-dimensional ``Area``.
Thus a feature/domain mismatch is possible independently of CSV publication.
The original table/source projection and materialization/role owners must
distinguish those cases. Root's #435 publication integration is relevant but
not standalone acceptance for this retained request. No source-feature rename,
scientific configuration advice or producer-result substitution is proposed.

Concrete independent compile-time defect
---------------------------------------

The registered FilterObjects removed-object option declares five trailing
artifact slots. Its callable return annotation has a fixed four-slot alternative
and an Ellipsis alternative; ``CellProfilerModuleCallableABI`` rejects Ellipsis
as absent exact positional evidence. Therefore it cannot validate the required
six-slot return, and the original compiler fails before execution. The two
determining files are unchanged across the three pinned sources.

The existing declaration/return owner must express its supported output shapes,
retaining exact types, order, source lineage and relationship direction. Do not
weaken the generic validator or add another positional roster beside the module.
Singer takes the declaration-side investigation; crossing Root's shared callable
or runtime files requires affirmative release/integration. Acceptance includes
default/removed/additional outputs, empty/nonempty labels, strict negative
cardinality/type controls and an independent declaration-only new case.

AST source evidence and limits
------------------------------

The original all-modules-at-once audit attempt was OOM-killed at its unchanged
512M limit, runtime9.037s, swap0B. Original stdout/stderr remain intact. The same
static source query was completed module-by-module using existing refactor-audit
Repository/ParsedModule owners and Python's AST, releasing each tree:

* All704 tracked OpenHCS Python files at each of the three pins parsed; zero
  parse omissions. All704 frozen-source files equal the retained installed
  target bytes. Main and Root comparison does not assert installed equality.
* Declaration/base/decorator/import/load/store reference sites for the relevant
  named owners and consumers were retained per module, with SHA256 source pins.
* Runtime34.543s, CPU34.242s, peak54.5M, swap0B, success/exit0, under one CPU,
  MemoryMax512M, MemorySwapMax0 and RuntimeMaxSec60. ``-I -S -B`` disables
  site/product imports and bytecode writes. Only standard library and existing
  static audit tooling ran; no scientific/native code was executed.
* Source AST is not execution/dataflow or dynamic-registry proof. Aliases and
  dynamic resolution remain semantic review obligations. Dependency gitlinks
  are recorded but their absent checkout sources were not scanned. This is not
  a complete NRA detector/R0/R1 or dependency-family admission.

Raw source evidence is retained under this checkout's
``validation/typed-label-plane-boundary/``. Streamed AST stdout SHA256:
91378977c719d39bb07519a466b26b3f1aaacb214e2de44327652dbc5e26d64d.
Original OOM stderr SHA256:
81de5438b061700a05d75e4281124d88ef2fa6852561e28fa88efecd15a8be77.
Successful guard stderr SHA256:
32dfe7015f138d408fb2f6f99799f55640a5bffcdbcb5c7159d037035d265ab0.

The independently supplied final producer required an additional targeted symbol
query rather than assuming it was the earlier watershed-library implementation.
Existing ParsedModule and FunctionFacts were reused, with Git selecting all
production files mentioning the related producer, domain, row-identity and
measurement-consumer names. The query includes declaration bases/decorators,
return annotations, imports, load/store sites and existing audit decision facts.
It parsed123 selected modules at frozen/main and125 at each Root source pin,
with zero parse omissions; it is not another global detector or behavioral run.
Runtime20.722s, CPU20.599s, peak43.9M, swap0B, exit0 under the same bounds.
Raw stdout SHA256:
e6c8f9f05069ddf14c09fcef6039e238036e75b583e895223791d98ca65d228b.
Raw guard stderr SHA256:
22d0c43215d0fbb4d3cdc0a27ef01cf04b3c9307f1633859a09d5b099b4d7bf1.

Root's subsequent published heads093c2f42d1235b5e218800f57937b6a52b4f5255 and
396379b06769a3f5afe92413b7d9d6a21dd3f66f have zero OpenHCS production-file
changes from the original audited2d3d75 head. This source equality does not
claim installed equivalence. The determining CPU producer, shape declarations,
row policy/projection, feature-query and FilterObjects/ABI bodies are unchanged
from the frozen source. Root's broader materialization/publication changes do
not introduce a label/ordinal correspondence at the inspected CSV boundary.

NRA/refactor-audit review lenses were BOUND-8 and BOUND-2 (carry and consume the
existing typed dimension/projection), IDEN-1 (object-ID scope versus image axes),
and IMPL-4/IMPL-12 (no partial family or duplicated slice procedure). No new
consumer switch, registry, compatibility path or provider/Numba modification
was introduced. Behavioral controls and installed acceptance await capacity and
the original integration owner's disposition; no tests were run here.

The authoritative refactor-audit ZIP includes BOUND-8; the installed catalog
copy does not yet include that newer entry. The ZIP, not the older copy, was
used for this lens. IDEN-1 is specifically relevant to a column answering both
categorical-ID and ordinal questions. No production mechanism has been copied,
removed or changed by this source-only checkpoint.

Byte-exact source log archive
----------------------------

``registered-object-output-source-20261003.tar.gz`` beside this receipt contains
the six original AST stdout/stderr files, including the unchanged OOM failure.
Its293982 bytes have SHA256:
c6f6184f9ae097c05542e187398c7c0b174c108feba087463ad035cec4214f1a.
All extracted member digests were checked against the original logs. This is
source evidence only, not a copy of scientific inputs, outputs or journals.
The original loose logs and local receiving receipt remain preserved.
