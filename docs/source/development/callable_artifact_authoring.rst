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

Image outputs that retain the current stack's axes should use
``MainFlowStackOutputSpec.output(name, ImageArtifactType, ...)``. The compiler
binds its lineage to the current image input. Declare the image before any
trailing table outputs so the returned image participates in main flow.
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
       ArtifactSpec, ImageArtifactType, MainFlowStackOutputSpec,
       MeasurementsArtifactType,
       ObjectLabelsArtifactType, ObjectMeasurementSubjectRelation,
       SourceStackLineageSourceRelation,
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
   FIXTURE_LABELS = ArtifactSpec.output(
       "fixture_labels", ObjectLabelsArtifactType,
       relations=(
           SourceStackLineageSourceRelation(source=FIXTURE_IMAGE.ref()),
       ),
       materialization=MaterializationSpec(ROIOptions(min_area=0)),
   )
   FIXTURE_ROWS = ArtifactSpec.output(
       "fixture_object_rows", MeasurementsArtifactType,
       measurement_feature_owner=FixtureFeatureOwner,
       relations=(
           ObjectMeasurementSubjectRelation(
               source=FIXTURE_LABELS.ref(), id_field="object_label",
           ),
           SourceStackLineageSourceRelation(source=FIXTURE_IMAGE.ref()),
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
exact labels output. ``SourceStackLineageSourceRelation`` preserves source
context and plane alignment; it is not an object-subject relation.
``MaterializationSourceIdentityRelation`` is supported for image targets, not
labels or measurements, and is therefore not attached to those outputs here.
``MainFlowStackOutputSpec`` additionally binds the image output to the compiled
current image input. ``PURE_2D`` asks the runtime to dispatch planes independently;
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
   from openhcs.core.runtime_output_matching import RuntimeReturnedOutputMatcher
   from openhcs.core.steps import FunctionStep

   fixture = np.zeros((8, 8), dtype=np.uint16)
   fixture[2:6, 3:7] = 1
   returned = inspect_label_fixture(fixture)
   contract = CallableContract.from_callable(inspect_label_fixture)
   matched = RuntimeReturnedOutputMatcher(contract, returned).resolve()
   assert np.array_equal(matched[FIXTURE_IMAGE.ref()], fixture)
   assert matched[FIXTURE_LABELS.ref()].dtype == np.int32
   assert matched[FIXTURE_ROWS.ref()].row_mappings() == (
       {"slice_index": 0, "object_label": 1, "pixel_count": 16},
   )
   step = FunctionStep(func=inspect_label_fixture)

For ordinary module authoring, import ``inspect_label_fixture`` from the module
where you saved it. For MCP custom registration, submit the complete declaration
block as ``source_code`` to ``openhcs_custom_function_register``; use the returned
``functions`` metadata (including ``function_id`` and ``import_path``) rather
than inventing a module path. Custom
callables are projected under ``openhcs.processing.custom_functions``. A local
helper class defined in that submitted source is not thereby a separately
importable symbol of that package. Keep the complete source together; do not add
``from openhcs.processing.custom_functions import FixtureObjectRow``. The
declaration deliberately uses evaluated annotations, without a future-annotations
import, so its dataclass schema is valid in the custom execution namespace as
well as in an ordinary module. Persist the source when it must survive a new
process; session-only registration does not make a spawned worker import it.

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
