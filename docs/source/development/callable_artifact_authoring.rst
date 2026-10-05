Callable and artifact authoring
===============================

A processing callable declares its ABI and semantic contract at the callable
boundary. ``CallableContract.from_callable`` snapshots those declarations once
for the compiler.

Callable contract
-----------------

The contract can carry input, output, and execution memory types, artifact
inputs and outputs, runtime-bound parameters, required variable components,
allowed grouping, processing contract, execution scope, runtime adapter,
preparation hook, and a callable request binding. The execution memory role is
the framework whose device scope must be active while the callable runs; it may
differ from an input or output conversion boundary. Use the existing decorators
and declaration helpers; do not teach compiler phases to inspect backend names.
A CellProfiler module resolves its dynamic artifact names into this same
contract rather than attaching another contract object.

Parameters supplied through artifact, configuration, runtime-context, or
adapter declarations are runtime-owned. The callable contract projects those
names into the shared python-introspect exclusion set used by catalogue and form
consumers. Declare the owning contract term; do not hide the parameter again in
a UI- or agent-owned list.

Configuration parameters can still receive an explicit per-function override;
semantic controls can select execution behaviour. The contract derives these
overridable names from configuration bindings and runtime parameter declarations.
Code generation preserves explicit settings while omitting injected objects.

Public keyword validation uses the canonical raw callable signature. When a
parameter annotation declares an enum, callers must provide a member of that
exact enum type. A string equal to the member's value is not the same nominal
declaration and is rejected before compilation.

Processing semantics
--------------------

Every callable that participates in normal image processing should declare a
``ProcessingContract``. It describes whether a call is local to a 2D plane or
depends on a wider stack. It does not select the stack axis: the step's
``ProcessingConfig.variable_components`` does that.

Semantic artifacts
------------------

Declare each semantic input/output as a role-neutral ``ArtifactSpec`` with a
nominal ``ArtifactType``. The enclosing ``artifact_inputs`` or
``artifact_outputs`` decorator binds that term to ``ArtifactInputPlan`` or
``ArtifactOutputPlan``; callers should not duplicate an otherwise identical
spec merely to assign its role. ``ArtifactSpec.input()`` and
``ArtifactSpec.output()`` remain explicit constructors when a pre-bound
reference is required. Relations and group/materialization sources point to
exact ``ArtifactSpecRef`` identities.

For CellProfiler declarations, use ``SettingToKeywordBinding.input()`` and
``SettingToKeywordBinding.output()`` for setting-backed artifact roles. Put
module-specific derivation in the leaf hooks supplied by
``CellProfilerModuleArtifactContracts``. The mixin resolves those declarations
into the invocation's ``CallableContract``. Source versus runtime satisfaction,
main-flow publication, and the active output subset are then represented by
compiled source, edge, and artifact plans; do not copy them into declaration
partitions.

Callable names such as ``special_inputs`` and ``special_outputs`` describe ABI
positions only. They are not a substitute for artifact types, producer edges,
or materialization declarations.

``special_inputs("labels")`` alone does not bind a required ``labels`` parameter.
Compilation rejects that incomplete contract, even if authored kwargs contain a
value for ``labels``. Declare its semantic input with
``artifact_inputs(ArtifactSpec.input("StoredLabels", ObjectLabelsArtifactType,
parameter_name="labels"))`` or supply the exact declaration through the existing
invocation-contract provider. Provider resolution precedes validation of the
finalized ``CallableContract``. An optional ABI parameter may instead retain its
declared Python default; the compiler does not invent an artifact identity,
runtime loader or default value for it.

Image outputs that retain the current stack's axes should use
``MainFlowStackOutputSpec.output(name, ImageArtifactType, ...)``. The compiler
binds their lineage to the current image input. Declare main-flow images before
trailing typed artifacts; multiple images share one aligned canonical return
slot, as described under **Return diagnostic images without flattening the ABI**.
For a cropped subset, return ``SelectedPlaneImageOutput(array, source_indices)``
in that image slot; the source indices must match the array's leading axis.
It is an array-compatible runtime payload: ``numpy.asarray(result)`` exposes
its pixels to code outside OpenHCS.

Typed table and object-label outputs
------------------------------------

A callable declaring ``MeasurementsArtifactType`` returns a schema-bearing
``ColumnarRows`` payload in the declared output position. Its ``fields`` and
physical ``columns`` must agree exactly in name and order; the runtime wraps the
payload in the measurement value carrying subject, source, and feature-owner
context. A measurement-producing declaration must also put its nominal
``RuntimeMeasurementFeatureOwner`` on the output ``ArtifactSpec``. Later
measurement consumers query that owner; they must not infer it from the
producer invocation name. Returning a bare list of dictionaries or relying on
a filename is not a measurement contract.

A callable declaring ``ObjectLabelsArtifactType`` returns the complete integer
label payload for that output. Runtime contextualization produces the nominal
``ObjectLabelValue``/``ObjectLabelSet`` with its domain, plane axis, source
spatial domain, and provenance. Do not return only an ROI sidecar or infer label
identity from the output tuple position. Multiple declared outputs must retain
their exact declaration order and artifact identities so compiled matching can
associate each runtime value with its producer.

Executable reference: image, labels and object rows
---------------------------------------------------

This reference inspects an **already-labelled synthetic 2D image**, with zero
as background and positive integers as object IDs. It is an ABI example, not a
segmentation algorithm. The image remains the first return position; labels and
object measurements occupy their explicitly declared trailing positions.

The complete declaration below can be saved in an importable Python module or
submitted as one custom-function source. Imports are explicit, including the
OpenHCS memory decorator (not ``numpy`` the array library). The nominal feature
owner queries the feature enum; there is no separate feature-name lookup table.
The dataclass owns the row schema, including the empty-row case.

.. code-block:: python
   :name: callable-artifact-reference

   from dataclasses import dataclass
   import numpy as np

   from openhcs.core.memory import numpy
   from openhcs.core.artifacts import (
       ImageArtifactType, MainFlowStackOutputSpec,
       MeasurementsArtifactType,
       ObjectLabelsArtifactType, ObjectMeasurementSubjectRelation,
   )
   from openhcs.core.measurement_row_materialization import (
       DataclassMeasurementColumnarRows,
   )
   from openhcs.core.pipeline.function_contracts import artifact_outputs
   from openhcs.core.runtime_measurements import (
       RuntimeMeasurementFeature, RuntimeMeasurementFeatureOwner,
   )
   from openhcs.processing.backends.lib_registry.unified_registry import (
       ProcessingContract,
   )
   from openhcs.processing.materialization import (
       CsvOptions, MaterializationSpec, ROIOptions,
   )

   class FixtureFeature(RuntimeMeasurementFeature):
       PIXEL_COUNT = "pixel_count"

   class FixtureFeatureOwner(RuntimeMeasurementFeatureOwner):
       @classmethod
       def owns_measurement_feature_name(cls, feature_name: str) -> bool:
           return any(feature.feature_name == feature_name
                      for feature in FixtureFeature)

       @classmethod
       def owns_primary_measurement_feature_name(cls, feature_name: str) -> bool:
           return cls.owns_measurement_feature_name(feature_name)

   @dataclass(frozen=True)
   class FixtureObjectRow:
       slice_index: int
       object_label: int
       pixel_count: int

   FIXTURE_IMAGE = MainFlowStackOutputSpec.output(
       "fixture_image", ImageArtifactType,
   )
   FIXTURE_LABELS = MainFlowStackOutputSpec.output(
       "fixture_labels", ObjectLabelsArtifactType,
       materialization=MaterializationSpec(ROIOptions(min_area=0)),
   )
   FIXTURE_ROWS = MainFlowStackOutputSpec.output(
       "fixture_object_rows", MeasurementsArtifactType,
       measurement_feature_owner=FixtureFeatureOwner,
       relations=(
           ObjectMeasurementSubjectRelation(
               source=FIXTURE_LABELS.ref(), id_field="object_label",
           ),
       ),
       materialization=MaterializationSpec(CsvOptions()),
   )

   @numpy(contract=ProcessingContract.PURE_2D)
   @artifact_outputs(FIXTURE_IMAGE, FIXTURE_LABELS, FIXTURE_ROWS)
   def inspect_label_fixture(
       image: np.ndarray,
   ) -> tuple[np.ndarray, np.ndarray, DataclassMeasurementColumnarRows]:
       """Inspect one pre-labelled plane without changing its image flow."""
       if image.ndim != 2 or not np.issubdtype(image.dtype, np.integer):
           raise ValueError("Expected a pre-labelled integer 2D fixture")
       if np.any(image < 0):
           raise ValueError("Fixture labels must be non-negative")
       labels = image.astype(np.int32, copy=True)
       rows = tuple(
           FixtureObjectRow(0, int(label), int(np.count_nonzero(labels == label)))
           for label in np.unique(labels) if label != 0
       )
       return image.copy(), labels, DataclassMeasurementColumnarRows(
           rows, row_type=FixtureObjectRow,
       )

``ObjectMeasurementSubjectRelation`` binds each row's ``object_label`` to the
exact labels output. ``MainFlowStackOutputSpec`` binds each output's source
context, group scope and plane alignment to the invocation's compiled image
input. It works for labels and rows as well as images; their artifact types
still determine their return positions and materialisation. An output image
reference is not an input-qualified group-scope source.
``MaterializationSourceIdentityRelation`` is supported for image targets, not
labels or measurements, and is therefore not attached to those outputs here.
``PURE_2D`` asks the runtime to dispatch planes independently;
the runtime projects the local ``slice_index=0`` rows onto the assembled stack's
plane axis. It does not create volumetric object identities.

The callable returns integer pixels and ``ColumnarRows``, not manually
constructed ``MeasurementTable`` or ``ObjectLabelValue`` instances. Runtime
contextualisation supplies those nominal wrappers, source provenance and spatial
domains. The ROI writer exports geometry from the complete label payload; an
ROI archive is not a replacement labels return. ``min_area=0`` here only keeps
the tiny fixture in the export and is not an analysis setting recommendation.
The CSV writer obtains field order from the dataclass carrier, without a copied
``CsvOptions.fields`` list. Persistence requires a configured materialisation
backend; the declarations alone do not write files during a direct Python call.

Minimal direct check and step declaration
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Run this after the declaration above. The direct call checks the Python ABI;
normal plate compilation/execution supplies image-source and runtime context.

.. code-block:: python
   :name: callable-artifact-reference-check

   from openhcs.core.callable_contract import CallableContract
   from openhcs.core.steps import FunctionStep

   fixture = np.zeros((8, 8), dtype=np.uint16)
   fixture[2:6, 3:7] = 1
   returned = inspect_label_fixture(fixture)
   contract = CallableContract.from_callable(inspect_label_fixture)
   matched = contract.resolve_returned_output(returned)
   assert np.array_equal(matched[FIXTURE_IMAGE.ref()], fixture)
   assert matched[FIXTURE_LABELS.ref()].dtype == np.int32
   assert matched[FIXTURE_ROWS.ref()].row_mappings() == (
       {"slice_index": 0, "object_label": 1, "pixel_count": 16},
   )
   step = FunctionStep(func=inspect_label_fixture)

For ordinary module authoring, import ``inspect_label_fixture`` from the module
where you saved it. For MCP custom registration, submit the complete declaration
block as ``source_code`` to the discovered ``openhcs_register_custom_function``
capability. Follow the ``openhcs_custom_function_workflow`` guide for explicit
endpoint, intended storage, preparation and uncertainty handling. Retain the
registration receipt, then describe the deliberately authored public function
identifier to verify its ``function_id``, ``import_path`` and artifact contract
rather than assuming registration returns a function catalogue. Custom
callables are projected under ``openhcs.processing.custom_functions``. A local
helper class defined in that submitted source is not thereby a separately
importable symbol of that package. Keep the complete source together; do not add
``from openhcs.processing.custom_functions import FixtureObjectRow``. The
declaration deliberately uses evaluated annotations, without a future-annotations
import, so its dataclass schema is valid in the custom execution namespace as
well as in an ordinary module. Persist the source when it must survive a new
process; session-only registration does not make a spawned worker import it.

Materialize typed 3D centres as feature-bearing Points
----------------------------------------------------

Points are a materialization of ``MeasurementsArtifactType``, not a missing
``PointsArtifactType`` or a centre-voxel image. Attach ``PointROIOptions`` to the
same object-measurement output as ``CsvOptions``. The existing writer projects
the contextualized table into source-bearing point ROIs; reopening that archive
uses the native Points route and retains row features, including object identity.
A CSV alone is not that native geometry declaration.

This declaration block is for an operation that already produces labels and
3D centre rows. It specifies their ABI, not how to detect or choose a centre:

.. code-block:: python
   :name: callable-artifact-points-reference

   from dataclasses import dataclass

   from openhcs.core.artifacts import (
       ImageArtifactType, MainFlowStackOutputSpec, MeasurementsArtifactType,
       ObjectLabelsArtifactType, ObjectMeasurementSubjectRelation,
   )
   from openhcs.core.measurement_row_materialization import (
       DataclassMeasurementColumnarRows,
   )
   from openhcs.core.runtime_measurements import (
       ObjectCoreMeasurementFeature, RuntimeMeasurementFeatureOwner,
   )
   from openhcs.processing.materialization import (
       CsvOptions, MaterializationSpec, PointROIOptions,
   )

   class CentreFeatureOwner(RuntimeMeasurementFeatureOwner):
       @classmethod
       def owns_measurement_feature_name(cls, feature_name: str) -> bool:
           return any(feature.feature_name == feature_name
                      for feature in ObjectCoreMeasurementFeature)

       @classmethod
       def owns_primary_measurement_feature_name(cls, feature_name: str) -> bool:
           return cls.owns_measurement_feature_name(feature_name)

   @dataclass(frozen=True)
   class CentreRow:
       object_label: int
       center_z: float
       center_y: float
       center_x: float

   CENTRE_IMAGE = MainFlowStackOutputSpec.output("centre_image", ImageArtifactType)
   CENTRE_LABELS = MainFlowStackOutputSpec.output(
       "centre_labels", ObjectLabelsArtifactType,
   )
   CENTRE_ROWS = MainFlowStackOutputSpec.output(
       "centre_rows", MeasurementsArtifactType,
       measurement_feature_owner=CentreFeatureOwner,
       relations=(ObjectMeasurementSubjectRelation(
           source=CENTRE_LABELS.ref(), id_field="object_label",
       ),),
       materialization=MaterializationSpec(
           CsvOptions(),
           PointROIOptions(
               z_feature=ObjectCoreMeasurementFeature.CENTER_Z,
               y_feature=ObjectCoreMeasurementFeature.CENTER_Y,
               x_feature=ObjectCoreMeasurementFeature.CENTER_X,
           ),
       ),
   )

On the existing centre-producing callable, declare
``@artifact_outputs(CENTRE_IMAGE, CENTRE_LABELS, CENTRE_ROWS)`` and return
``image, labels, DataclassMeasurementColumnarRows(rows, row_type=CentreRow)``.
Use the existing memory/processing decorators, as in the executable reference;
``PURE_3D`` is appropriate only for an actual volumetric calculation. Retain
the complete source bindings and compiled ZYX grouping: the decorator alone
does not establish axis order. The row's representative rule (peak, body centre
or another task-defined location) remains the analysis contract, not the writer.

Coordinates are floating source-grid Z/Y/X locations, not calibrated world
coordinates and not a manually rescaled display array. Keep the full declared
source Z domain, including planes without objects, and its source paths,
spatial frame and voxel spacing through the compiled source/subject relations.
The writer rejects missing source provenance, missing/foreign coordinate fields,
duplicate object IDs and non-finite coordinates. It currently rejects an empty
Points archive; empty measurement rows retain their table schema but do not
establish successful point materialization.

Fractional Z is geometry. An integer navigation slice, a rounded centre-voxel
marker image and a fractional point table describe different things. Do not
round the table to fit a viewer slice or infer its Z domain from occupied
labels/rounded markers. Compare the persisted table/archive and native Points
at matched raw coordinates, full Z extent and orthogonal views; inspect object
IDs/features and source calibration, not just point count. Verify that the
installed version exposes the required point producer/domain and viewer geometry
contracts before relying on automatic streaming or archive reopening. Declaration
and direct-call checks do not prove that live path.

Return diagnostic images without flattening the ABI
--------------------------------------------------

``MainFlowStackOutputSpec`` declares source lineage; it does not give every
Image its own outer tuple slot. ``CallableContract`` groups the consecutive
leading main-flow Image declarations into one canonical return slot. Labels,
measurements and other remaining artifact declarations each have one trailing
slot in their exact order. Inspect ``canonical_return_output_specs`` and
``trailing_return_output_specs`` before extending a callable's returns.

For example, to extend the executable 2D reference with an aligned diagnostic,
keep its labels/rows declarations and replace its image declarations/decorator:

.. code-block:: python
   :name: callable-artifact-diagnostic-reference

   from openhcs.core.aligned_image_payload import (
       AlignedImageSliceContext, pack_aligned_image_outputs,
   )

   FIXTURE_DIAGNOSTIC = MainFlowStackOutputSpec.output(
       "fixture_diagnostic", ImageArtifactType,
   )

   @numpy(contract=ProcessingContract.PURE_2D)
   @artifact_outputs(
       FIXTURE_IMAGE, FIXTURE_DIAGNOSTIC, FIXTURE_LABELS, FIXTURE_ROWS,
   )
   def inspect_label_fixture_with_diagnostic(image: np.ndarray):
       image, labels, rows = inspect_label_fixture(image)
       image_specs = (FIXTURE_IMAGE, FIXTURE_DIAGNOSTIC)
       main_images = pack_aligned_image_outputs(
           (image, (labels > 0).astype(np.uint8)),
           slice_contexts=AlignedImageSliceContext.main_flow_for_artifact_specs(
               image_specs,
           ),
       )
       return main_images, labels, rows

The diagnostic here is only the synthetic fixture's foreground indicator.
The helper retains exact named slice contexts; it is not ``np.stack`` of
scientific Z planes and introduces no new return codec. With five leading
main-flow Images followed by three typed artifacts, the outer return has four
positions (one aligned image bundle plus three artifacts), not eight. A
``trailing return count`` error is repaired against this declared partition,
not by dropping useful diagnostics or weakening the matcher. Validate/compile
the corrected complete document and inspect its materialization/streaming plan;
this ABI repair does not itself settle a viewer or validate the analysis.

Consume a nominal artifact input
-------------------------------

An artifact's input ABI is not necessarily its raw output representation.
``ObjectLabelsArtifactType`` accepts integer labels from a producer, but supplies
the consumer with ``ObjectLabelValue`` (including its named ``ObjectLabelSet``
subclass). The value carries object IDs, plane/domain and source provenance;
being array-compatible does not make ``np.ndarray`` a valid input annotation.
Query the artifact type's ``runtime_parameter_types()`` or the reflected input
contract rather than inferring it from dtype or a saved file extension.

This complete consumer masks an aligned image with the already-declared
``fixture_labels`` from the preceding example. It does not detect objects or
choose analysis settings. Save it in an importable module or submit this block
as its own custom-function source:

.. code-block:: python
   :name: callable-artifact-input-reference

   import numpy as np

   from openhcs.core.memory import numpy
   from openhcs.core.artifacts import ArtifactSpec, ObjectLabelsArtifactType
   from openhcs.core.pipeline.function_contracts import artifact_inputs
   from openhcs.core.runtime_object_labels import ObjectLabelValue
   from openhcs.processing.backends.lib_registry.unified_registry import (
       ProcessingContract,
   )

   STORED_LABELS = ArtifactSpec.input(
       "fixture_labels", ObjectLabelsArtifactType, parameter_name="objects",
   )

   @numpy(contract=ProcessingContract.PURE_2D)
   @artifact_inputs(STORED_LABELS)
   def mask_declared_objects(
       image: np.ndarray, *, objects: ObjectLabelValue,
   ) -> np.ndarray:
       """Mask one aligned image plane using its nominal object-label input."""
       label_pixels = np.asarray(objects)
       return np.where(label_pixels > 0, image, 0)

``objects`` is supplied by the compiled artifact edge, not a ``FunctionStep``
keyword containing an array, file path or copied labels. The declaration's
semantic name/type select the producer; ``parameter_name`` binds that input
to the callable argument. Use ``FunctionStep(func=mask_declared_objects)`` after
the compatible producer, retaining the complete pipeline configuration/source
bindings. ``np.asarray(objects)`` is a local pixel view for this calculation,
not a replacement for the nominal input or its provenance. If the task needs
object/plane identity, use the value's domain and plane APIs rather than
reconstructing them from dense pixels. ``PURE_2D`` here describes locality;
it does not select the pipeline's variable axis.

Repair the earliest failed declaration before trying execution. If compilation
says a parameter ``does not accept object_labels artifact payloads``, inspect
that input's annotation and declared runtime type: change an erroneous
``objects: np.ndarray`` to ``objects: ObjectLabelValue`` and keep the exact
artifact binding. A cast inside the function cannot repair admission that fails
before the function runs. Removing the annotation, changing the artifact to an
image, or hand-loading a file hides the mismatch rather than fixing it.
For ``no exact artifact declaration binding`` or an unavailable producer,
repair the declared name/type/parameter or producer edge instead; the annotation
alone does not bind an artifact. Retain the failed source and validate/compile
the corrected complete document through the ordinary route. This establishes
technical input compatibility, not object identity or biological accuracy.

Summarize declared measurements once per plate
---------------------------------------------

A terminal ``PLATE`` callable receives ``RuntimeArtifactBatch``, not an image
or a directory of CSVs. The parent executes it once after the compiled axes
complete, selecting records through its exact artifact input declarations.
The existing ``ExportToSpreadsheet`` implementation uses this same ABI.
Do not add ``@numpy`` or a ``ProcessingContract``: these declare axis-local
image processing and are rejected for plate scope.

This complete custom-function source summarizes the preceding example's
``fixture_object_rows``. It reports record and measurement-row counts per
runtime axis, not biological object counts or an inferred well identity:

.. code-block:: python
   :name: callable-artifact-plate-reference

   from dataclasses import dataclass
   from typing import cast

   from openhcs.core.artifacts import (
       ArtifactSpec, MeasurementsArtifactType, SpecialArtifactType,
   )
   from openhcs.core.callable_contract import FunctionStepExecutionScope
   from openhcs.core.measurement_row_materialization import (
       DataclassMeasurementColumnarRows,
   )
   from openhcs.core.pipeline.function_contracts import (
       artifact_inputs, artifact_outputs, execution_scope, runtime_bound_parameters,
   )
   from openhcs.core.runtime_measurements import MeasurementTable
   from openhcs.core.runtime_stores import RuntimeArtifactBatch
   from openhcs.processing.materialization import CsvOptions, MaterializationSpec

   @dataclass(frozen=True)
   class PlateSummaryRow:
       axis_id: str
       record_count: int
       measurement_row_count: int

   PLATE_ROWS = ArtifactSpec.input("fixture_object_rows", MeasurementsArtifactType)
   PLATE_SUMMARY = ArtifactSpec.output(
       "fixture_plate_summary", SpecialArtifactType,
       materialization=MaterializationSpec(CsvOptions()),
   )

   @execution_scope(FunctionStepExecutionScope.PLATE)
   @runtime_bound_parameters(RuntimeArtifactBatch)
   @artifact_inputs(PLATE_ROWS)
   @artifact_outputs(PLATE_SUMMARY)
   def summarize_fixture_plate(
       *, artifact_batch: RuntimeArtifactBatch,
   ) -> DataclassMeasurementColumnarRows:
       """Summarize only the declared measurement records from this execution."""
       rows = tuple(
           PlateSummaryRow(
               axis_id, len(records),
               sum(cast(MeasurementTable, record.data).rows.row_count() for record in records),
           )
           for axis_id, records in artifact_batch.records(PLATE_ROWS.ref()).items()
       )
       return DataclassMeasurementColumnarRows(rows, row_type=PlateSummaryRow)

Submit this block as its own source through the existing custom registration
route, or import it from a module. Describe the returned registry ID to verify
``PLATE`` scope, then append ``FunctionStep(func=summarize_fixture_plate)`` to
the complete pipeline after the compatible measurement producer. Retain its
configuration/source bindings; no axis-scoped step may follow a plate step.
``artifact_batch`` is required, keyword-only and runtime-owned: do not supply
it in authored kwargs. Its ``records(spec.ref())`` exposes typed
``StoredRuntimeValue`` records by axis; each selected measurement payload is a
``MeasurementTable`` at ``record.data`` whose rows retain their schema. The cast
expresses the declared measurement input type; it does not load or convert data.
No file loading, guessed
paths, bare dictionary return or ``Any`` annotation is needed.

The current plate executor requires exactly one ``SpecialArtifactType`` output;
it does not support a plate-scoped ``MeasurementsArtifactType`` output.
Here that side-channel payload is schema-bearing ``ColumnarRows``, which the
existing CSV materializer renders without a custom writer. It is not a new
object-measurement table or object-label domain. An empty table contributes
zero rows without losing its schema;
unavailable required inputs are a binding error, not a reason to scan files.
Repair the earliest validation/compile error against these exact decorators,
batch annotation and producer reference. A successful summary covers the
compiled execution's records; it does not establish whole-task coverage from
partially persisted files or prove biological validity.

Verification
------------

- Build ``CallableContract.from_callable`` and assert its typed declarations.
- Validate public kwargs with exact enum members and assert that equivalent raw
  strings are rejected when the callable declares an enum annotation.
- Assert all declared input, output, and execution memory roles when framework
  conversion or device execution is part of the ABI.
- For a CellProfiler module, derive its invocation ``CallableContract`` and
  assert the setting-resolved specs and relations.
- Compile a minimal ``FunctionStep`` and inspect its artifact input/output plans.
- Execute a focused case when runtime-bound parameters or an adapter changed.
- For stack-transforming outputs, execute both first-step and chained cases;
  inspect saved pixel values and source-coordinate filenames, including a
  reordered or reduced plane selection.

See :doc:`../architecture/artifact_contract_system`.
