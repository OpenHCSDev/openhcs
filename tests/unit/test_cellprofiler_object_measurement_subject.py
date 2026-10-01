"""Object-subject declarations compose without measurement input policies."""

from __future__ import annotations

import pytest

from openhcs.core.artifacts import (
    ArtifactSpec,
    ArtifactSpecCollection,
    ArtifactSpecRelation,
    ImageArtifactType,
    MeasurementsArtifactType,
    ObjectLabelsArtifactType,
    ObjectMeasurementSubjectRelation,
)
from openhcs.core.function_patterns import DEFAULT_GROUP_KEY, FunctionInvocationKey
from openhcs.core.invocation_artifacts import ArtifactDeclarationStepContext
from openhcs.core.memory.decorators import numpy
from openhcs.core.runtime_measurements import MeasurementScope
from openhcs.interop.cellprofiler.module_artifact_declarations import (
    MeasurementArtifactOutputModule,
    ObjectArtifactInputModule,
    ObjectMeasurementArtifactOutputModule,
    ObjectMeasurementInputModule,
)
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.interop.cellprofiler.parser import ModuleBlock
from openhcs.interop.cellprofiler.runtime.measurement_recording import (
    NoObjectNameMeasurementRecordMixin,
)
from openhcs.processing.backends.cellprofiler.classification import (
    ClassifyObjectsSingleMeasurementModule,
)
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract


@numpy(contract=ProcessingContract.PURE_3D)
def _object_subject_probe(image):
    return image


class _ObjectSubjectProbeModule(
    NoObjectNameMeasurementRecordMixin,
    ObjectArtifactInputModule,
    ObjectMeasurementArtifactOutputModule,
):
    """New declaration using only existing capabilities and its own names."""

    module_name = "ObjectSubjectCapabilityProbe"
    function_name = "_object_subject_probe"


def _measurement_output(module_type, inputs, function_name=None):
    return module_type.measurement_output_artifact(
        ModuleBlock(module_num=1, name=module_type.module_name),
        invocation_key=FunctionInvocationKey(
            function_name or module_type.function_name, DEFAULT_GROUP_KEY, 0
        ),
        step_context=ArtifactDeclarationStepContext.empty(),
        artifact_inputs=ArtifactSpecCollection(inputs),
    )


@pytest.mark.parametrize(
    "function_name", ClassifyObjectsSingleMeasurementModule.declared_function_names()
)
def test_classification_variants_declare_only_exact_object_subject(function_name):
    image = ArtifactSpec.input("SourceImage", ImageArtifactType)
    objects = ArtifactSpec.input("Cells", ObjectLabelsArtifactType)
    prior = ArtifactSpec.input("PriorMeasurements", MeasurementsArtifactType)
    output = _measurement_output(
        ClassifyObjectsSingleMeasurementModule, (image, objects, prior), function_name
    )

    subjects = ArtifactSpecRelation.measurement_subjects_for_output(output)
    assert len(subjects) == 1
    assert subjects[0].scope is MeasurementScope.OBJECT
    assert subjects[0].name == objects.name
    assert ObjectMeasurementSubjectRelation(objects.ref()) in output.relations
    assert all(
        ArtifactSpecRelation(spec.ref()) in output.relations
        for spec in (image, objects, prior)
    )
    assert output.measurement_feature_owner is ClassifyObjectsSingleMeasurementModule
    assert (
        ClassifyObjectsSingleMeasurementModule.measurement_record_object_name(
            None, None
        )
        is None
    )


def test_new_declaration_derives_subject_from_original_capability_and_registry():
    declaration = CellProfilerModule.require_module("ObjectSubjectCapabilityProbe")
    objects = ArtifactSpec.input("AnotherObjectSet", ObjectLabelsArtifactType)
    output = _measurement_output(declaration, (objects,))

    subject = MeasurementsArtifactType.require_output_subject(output)
    assert subject.scope is MeasurementScope.OBJECT
    assert subject.name == objects.name
    assert output.measurement_feature_owner is declaration
    assert declaration.measurement_record_object_name(None, None) is None
    assert declaration.declared_setting_bindings() == ()
    assert declaration.__mro__.index(
        ObjectMeasurementArtifactOutputModule
    ) < declaration.__mro__.index(MeasurementArtifactOutputModule)
    assert (
        ObjectMeasurementInputModule.measurement_output_relations.__func__
        is ObjectMeasurementArtifactOutputModule.measurement_output_relations.__func__
    )


def test_classification_does_not_inherit_measurement_input_setting_or_splitting():
    declaration = ClassifyObjectsSingleMeasurementModule
    assert not issubclass(declaration, ObjectMeasurementInputModule)
    assert declaration.declared_setting_bindings() == declaration.setting_bindings
    assert (
        ObjectMeasurementInputModule.object_measurement_binding
        not in declaration.declared_setting_bindings()
    )
    block = ModuleBlock(module_num=1, name=declaration.module_name)
    assert declaration.invocation_module_blocks(block) == (block,)


@pytest.mark.parametrize(
    "module_type", (_ObjectSubjectProbeModule, ClassifyObjectsSingleMeasurementModule)
)
def test_missing_object_subject_stays_rejected(module_type):
    output = _measurement_output(
        module_type, (ArtifactSpec.input("NotAnObject", ImageArtifactType),)
    )
    with pytest.raises(ValueError, match="no declared measurement subject relation"):
        MeasurementsArtifactType.validate_native_output_declaration(output)


@pytest.mark.parametrize(
    "module_type", (_ObjectSubjectProbeModule, ClassifyObjectsSingleMeasurementModule)
)
def test_ambiguous_object_subject_stays_rejected(module_type):
    output = _measurement_output(
        module_type,
        tuple(
            ArtifactSpec.input(name, ObjectLabelsArtifactType)
            for name in ("Cells", "Nuclei")
        ),
    )
    with pytest.raises(ValueError, match="multiple measurement subjects"):
        MeasurementsArtifactType.validate_native_output_declaration(output)
