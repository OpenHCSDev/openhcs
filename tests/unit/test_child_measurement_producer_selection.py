"""Prior child measurements select their producer domain, not the child channel."""

from dataclasses import replace

import pytest

from openhcs.constants.constants import AllComponents
from openhcs.core.artifacts import (
    ArtifactInputPlan,
    ArtifactOutputPlan,
    ArtifactSpec,
    ArtifactSpecCollection,
    MeasurementsArtifactType,
    ObjectLabelsArtifactType,
    ObjectMeasurementSubjectRelation,
)
from openhcs.core.component_group_scope import (
    ComponentGroupScope,
    RuntimeExecutionAxisScope,
)
from openhcs.core.component_set import ComponentSet
from openhcs.core.function_patterns import (
    CompiledFunctionInvocation,
    InvocationArtifactInputProjectionKey,
    FunctionInvocationKey,
    DEFAULT_GROUP_KEY,
)
from openhcs.core.pipeline.path_planner import (
    PathPlannerArtifactStage,
    PathPlannerGroupScope,
)
from openhcs.core.source_bindings import EMPTY_SOURCE_BINDINGS
from openhcs.processing.backends.cellprofiler.relationships import RelateObjectsModule
from tests.unit.test_cellprofiler_relationship_contracts import _contract, _module


def _declared_input(*, enabled=True):
    parent = ArtifactSpec.input("Parents", ObjectLabelsArtifactType)
    child = ArtifactSpec.input("Children", ObjectLabelsArtifactType)
    measurements = ArtifactSpec.output(
        "intensity",
        MeasurementsArtifactType,
        relations=(ObjectMeasurementSubjectRelation(child.ref()),),
    )
    contract = _contract(
        RelateObjectsModule,
        _module(
            8,
            "RelateObjects",
            {
                "Select the parent objects": parent.name,
                "Select the child objects": child.name,
                "Calculate child-parent distances?": "None",
                "Calculate distances to other parents?": "No",
                "Calculate per-parent means for all child measurements?": (
                    "Yes" if enabled else "No"
                ),
            },
        ),
        inputs=(parent, child, measurements),
    )
    return contract, child


def _compiled_edge(*, dynamic=False, declared=True):
    contract, child = _declared_input()
    spec = contract.artifact_inputs.of_artifact_type(MeasurementsArtifactType)[0]
    if not declared:
        spec = replace(spec, relations=())
    storage = ArtifactInputPlan(
        name=spec.name,
        path="/memory/intensity.pkl",
        artifact_type=MeasurementsArtifactType,
        group_keys=(None,) if dynamic else ("1", "2", "5", "3"),
        group_component=AllComponents.CHANNEL,
        paths_by_group=(
            None
            if dynamic
            else {key: f"/memory/intensity_{key}.pkl" for key in ("1", "2", "5", "3")}
        ),
        source_step_id=7,
    )
    invocation = CompiledFunctionInvocation(
        key=FunctionInvocationKey.from_contract(contract, DEFAULT_GROUP_KEY, 0),
        contract=contract,
    )
    index = next(
        i
        for i, value in enumerate(contract.artifact_inputs)
        if value.ref() == spec.ref()
    )
    edge = PathPlannerArtifactStage(None).invocation_input_edge(
        invocation,
        InvocationArtifactInputProjectionKey(invocation.key, index),
        input_spec=spec,
        storage_plan=storage,
        invocation_scope=PathPlannerGroupScope.from_raw(
            ("3",), component=AllComponents.CHANNEL
        ),
        relation_source_scopes={},
        consumer_variable_components=ComponentSet((AllComponents.SITE,)),
        source_bindings=EMPTY_SOURCE_BINDINGS,
        available_artifacts=ArtifactSpecCollection(()),
        consumes_main_flow=False,
    )
    return edge, child


def test_relate_prior_child_measurements_compile_all_source_channels():
    edge, _ = _compiled_edge()
    assert (
        edge.projection.producer_selection_scope
        == edge.storage_plan.producer_group_scope()
    )
    assert edge.projection.consumer_variable_components == (AllComponents.SITE,)


def test_ordinary_measurement_input_still_selects_invocation_channel():
    edge, _ = _compiled_edge(declared=False)
    assert edge.projection.producer_selection_scope == ComponentGroupScope.from_raw(
        ("3",),
        component=AllComponents.CHANNEL,
    )


def test_disabled_parent_means_add_no_measurement_inputs():
    contract, _ = _declared_input(enabled=False)
    assert contract.artifact_inputs.of_artifact_type(MeasurementsArtifactType) == ()


from openhcs.core.runtime_stores import RuntimeArtifactInput, RuntimeValueStore
from openhcs.core.runtime_artifact_values import RuntimeValue
from openhcs.core.runtime_measurements import (
    MeasurementScope,
    MeasurementSubject,
    MeasurementTable,
)
from openhcs.core.measurement_row_materialization import MeasurementSparseColumnarRows
from openhcs.core.runtime_tabular_values import FieldSpec
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_matching import SourceImageSetIdentityPolicy
from openhcs.core.source_plane_alignment import SourcePlaneIdentitySequenceAlignment
from openhcs.core.source_bindings import (
    CompiledSourceBindingPlan,
    NamedSourceBinding,
    ComponentSelector,
)


def _measurement_store(edge, *, well="A01", fixed=()):
    store = RuntimeValueStore()
    for channel in ("1", "2", "5", "3"):
        path = edge.storage_plan.path_for_runtime_query(channel)
        plan = ArtifactOutputPlan(
            name="intensity",
            path=path,
            artifact_type=MeasurementsArtifactType,
            group_keys=(channel,),
            group_component=AllComponents.CHANNEL,
        )
        for subject in ("Children", "Unrelated"):
            table = MeasurementTable(
                name="intensity",
                source_image_name=f"Orig{channel}",
                subject=MeasurementSubject(MeasurementScope.OBJECT, subject),
                rows=MeasurementSparseColumnarRows.from_rows(
                    ({"object_label": 1, "value": float(channel)},),
                    fields=(FieldSpec("object_label", int), FieldSpec("value", float)),
                ),
            )
            store.record(
                RuntimeValue.normalize_for_execution_scope(
                    plan,
                    table,
                    execution_scope=RuntimeExecutionAxisScope.from_raw(
                        well,
                        component=AllComponents.CHANNEL,
                        value=channel,
                        fixed_component_values=fixed,
                    ),
                ),
                path=path,
                backend="memory",
            )
    return store


def _runtime_input(edge, *, fixed=()):
    return RuntimeArtifactInput(
        edge_plan=edge,
        backend="memory",
        axis_scope=RuntimeExecutionAxisScope.from_raw(
            "A01",
            component=AllComponents.CHANNEL,
            value="3",
            fixed_component_values=fixed,
        ),
    )


@pytest.mark.parametrize("dynamic", (False, True))
def test_declared_child_measurements_gather_all_exact_producer_channels(dynamic):
    edge, _ = _compiled_edge(dynamic=dynamic)
    records = _runtime_input(edge).records(_measurement_store(edge))
    assert [record.key.scope.value_text for record in records] == [
        "1",
        "1",
        "2",
        "2",
        "5",
        "5",
        "3",
        "3",
    ]
    from openhcs.interop.cellprofiler.runtime.object_measurement_tables import (
        ObjectMeasurementTableIndex,
    )

    children = ObjectMeasurementTableIndex.from_tables(
        tuple(record.value.data for record in records)
    ).for_object("Children")
    assert [table.source_image_name for table in children] == [
        "Orig1",
        "Orig2",
        "Orig5",
        "Orig3",
    ]


def test_ordinary_dynamic_input_keeps_current_channel_selection():
    edge, _ = _compiled_edge(dynamic=True, declared=False)
    records = _runtime_input(edge).records(_measurement_store(edge))
    assert [record.key.scope.value_text for record in records] == ["3", "3"]


@pytest.mark.parametrize("dynamic", (False, True))
@pytest.mark.parametrize(
    "component", (AllComponents.SITE, AllComponents.TIMEPOINT, AllComponents.Z_INDEX)
)
def test_complete_measurement_selection_rejects_other_fixed_context(dynamic, component):
    edge, _ = _compiled_edge(dynamic=dynamic)
    with pytest.raises(RuntimeError, match="Missing .*artifact input"):
        _runtime_input(edge, fixed=((component, "1"),)).records(
            _measurement_store(edge, fixed=((component, "2"),))
        )


@pytest.mark.parametrize("dynamic", (False, True))
def test_complete_measurement_selection_rejects_another_well(dynamic):
    edge, _ = _compiled_edge(dynamic=dynamic)
    with pytest.raises(RuntimeError, match="Missing .*artifact input"):
        _runtime_input(edge).records(_measurement_store(edge, well="B01"))


def _source_axis(channel, *, sites=("1", "2"), well="A01", time="1"):
    provenance = SourceImageProvenancePlanes.from_components(
        component_metadata=tuple(
            {
                "well": well,
                "site": site,
                "channel": channel,
                "timepoint": time,
                "z_index": "1",
            }
            for site in sites
        )
    )
    from openhcs.core.source_image_provenance import SourceImageProvenance

    bindings = CompiledSourceBindingPlan(
        bindings=tuple(
            NamedSourceBinding(
                alias=f"Orig{value}",
                component_identity=(ComponentSelector(AllComponents.CHANNEL, value),),
            )
            for value in ("1", "2", "5", "3")
        )
    )
    policy = SourceImageSetIdentityPolicy.from_source_bindings(bindings)
    return SourceImageProvenance(
        source_image_provenance_planes=provenance
    ).image_set_axis(policy)


def test_cross_channel_alignment_retains_two_sites_with_reused_object_ids():
    child_axis = _source_axis("3")
    assert len(child_axis) == 2
    for channel in ("1", "2", "5", "3"):
        assert SourcePlaneIdentitySequenceAlignment(
            _source_axis(channel, sites=("2", "1")),
            child_axis,
        ).target_indexes_for_image_planes() == (1, 0)


@pytest.mark.parametrize("kwargs", ({"well": "B01"}, {"time": "2"}, {"sites": ("3",)}))
def test_child_measurement_alignment_rejects_foreign_or_ambiguous_planes(kwargs):
    assert (
        SourcePlaneIdentitySequenceAlignment(
            _source_axis("1", **kwargs),
            _source_axis("3"),
        ).target_indexes_for_image_planes()
        is None
    )


def test_child_measurement_alignment_rejects_ambiguous_target_occurrences():
    target = _source_axis("3")[0]
    assert (
        SourcePlaneIdentitySequenceAlignment(
            _source_axis("1", sites=("1",)),
            (target, target),
        ).target_indexes_for_image_planes()
        is None
    )


def _upstream_rows(*, sites=("1", "2"), well="A01", time="1"):
    import numpy as np
    from openhcs.core.runtime_object_labels import (
        ObjectLabelSet,
        ObjectLabelVariantData,
    )
    from openhcs.core.runtime_object_label_domains import (
        ObjectLabelDomain,
        ObjectLabelDomainScope,
    )
    from openhcs.core.runtime_plane_projection import (
        RuntimePlaneAxis,
        RuntimePlaneProjection,
    )
    from openhcs.core.function_patterns import InvocationArtifactInputEdgePlan
    from openhcs.core.runtime_image_values import ImagePayloadMetadata
    from openhcs.core.artifacts import RelationshipsArtifactType
    from openhcs.interop.cellprofiler.runtime.invocation import CellProfilerImageRequest
    from openhcs.interop.cellprofiler.runtime.output_record_request import (
        CellProfilerOutputRecordRequest,
    )
    from openhcs.processing.backends.cellprofiler.relationships import (
        RelateObjectsRelationshipMeasurementRows,
    )
    from openhcs.processing.backends.cellprofiler.intensity import (
        MeasureObjectIntensityModule,
    )
    from tests.unit.cellprofiler_runtime_test_support import (
        cellprofiler_runtime_adapter_for_test,
    )

    contract, child = _declared_input()
    measurement_edge, _ = _compiled_edge()
    child = contract.artifact_inputs.of_artifact_type(ObjectLabelsArtifactType)[1]
    child_planes = SourceImageProvenancePlanes.from_components(
        component_metadata=tuple(
            {
                "well": "A01",
                "site": site,
                "channel": "3",
                "timepoint": "1",
                "z_index": "1",
            }
            for site in ("1", "2")
        )
    )
    labels = ObjectLabelSet(
        name=child.name,
        variant_data=ObjectLabelVariantData(
            labels=np.array([[[1, 2], [0, 0]], [[1, 2], [0, 0]]], dtype=np.int32)
        ),
        domain=ObjectLabelDomain(
            scope=ObjectLabelDomainScope.PLANE,
            declared_object_id_domains=((1, 2), (1, 2)),
        ),
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_provenance_planes=child_planes,
    )
    storage = ArtifactInputPlan(
        name=child.name,
        path="/memory/children.pkl",
        artifact_type=ObjectLabelsArtifactType,
        group_keys=("3",),
        group_component=AllComponents.CHANNEL,
        variable_components=(AllComponents.SITE,),
        source_step_id=1,
    )
    child_edge = InvocationArtifactInputEdgePlan(
        key=InvocationArtifactInputProjectionKey(
            measurement_edge.key.invocation_key, 1
        ),
        spec=child,
        storage_plan=storage,
        projection=replace(
            measurement_edge.projection,
            producer_selection_scope=storage.producer_group_scope(),
        ),
    )
    store = RuntimeValueStore()
    plan = ArtifactOutputPlan(
        name=child.name,
        path=storage.path,
        artifact_type=ObjectLabelsArtifactType,
        group_keys=("3",),
        group_component=AllComponents.CHANNEL,
        variable_components=(AllComponents.SITE,),
    )
    store.record(
        RuntimeValue.normalize(plan, labels, axis_id="A01"),
        path=plan.path,
        backend="memory",
    )
    for channel in ("1", "2", "5", "3"):
        name = f"Orig{channel}"
        feature = f"Intensity_MeanIntensity_{name}"
        planes = SourceImageProvenancePlanes.from_components(
            component_metadata=tuple(
                {
                    "well": well,
                    "site": site,
                    "channel": channel,
                    "timepoint": time,
                    "z_index": "1",
                }
                for site in sites
            )
        )
        path = measurement_edge.storage_plan.path_for_runtime_query(channel)
        output = ArtifactOutputPlan(
            name="intensity",
            path=path,
            artifact_type=MeasurementsArtifactType,
            group_keys=(channel,),
            group_component=AllComponents.CHANNEL,
        )
        for subject in ("Children", "Unrelated"):
            table = MeasurementTable(
                name="intensity",
                subject=MeasurementSubject(MeasurementScope.OBJECT, subject),
                source_image_name=name,
                measurement_feature_owner=MeasureObjectIntensityModule,
                source_image_provenance_planes=planes,
                rows=MeasurementSparseColumnarRows.from_rows(
                    tuple(
                        {
                            "slice_index": index,
                            "object_label": label,
                            feature: float(int(channel) * 100 + int(site) * 10 + label),
                        }
                        for index, site in enumerate(sites)
                        for label in (1, 2)
                    ),
                    fields=(
                        FieldSpec("slice_index", int),
                        FieldSpec("object_label", int),
                        FieldSpec(feature, float),
                    ),
                ),
            )
            store.record(
                RuntimeValue.normalize(output, table, axis_id="A01"),
                path=path,
                backend="memory",
            )
    image = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_provenance_planes=child_planes,
    ).payload_with(np.ones((2, 2, 2), dtype=np.float32))
    bindings = CompiledSourceBindingPlan(
        bindings=tuple(
            NamedSourceBinding(
                alias=f"Orig{channel}",
                component_identity=(ComponentSelector(AllComponents.CHANNEL, channel),),
            )
            for channel in ("1", "2", "5", "3")
        )
    )
    adapter = cellprofiler_runtime_adapter_for_test(
        runtime_value_store=store,
        callable_contract=contract,
        artifact_inputs={edge.key: edge for edge in (child_edge, measurement_edge)},
        axis_scope=RuntimeExecutionAxisScope.from_raw(
            "A01", component=AllComponents.CHANNEL, value="3"
        ),
        source_image_set_identity_policy=SourceImageSetIdentityPolicy.from_source_bindings(
            bindings
        ),
        source_payload=image,
        plane_projection=RuntimePlaneProjection.stack(2),
    )
    spec = contract.artifact_outputs.of_artifact_type(RelationshipsArtifactType)[0]
    output = ArtifactOutputPlan(
        name=spec.name,
        path="/memory/relationships.pkl",
        artifact_type=RelationshipsArtifactType,
        relations=spec.relations,
    )
    request = CellProfilerOutputRecordRequest(
        callable_contract=contract,
        active_input_edges=(child_edge, measurement_edge),
        adapter=adapter,
        spec=spec,
        output_plan=output,
        output_value=None,
        source=CellProfilerImageRequest(
            source_image_name="Orig3",
            source_aliases=("Orig3",),
            image_count=2,
            payload=image,
        ),
        call_kwargs={},
        current_image=image,
    )
    return RelateObjectsRelationshipMeasurementRows(request), child, contract


def test_actual_upstream_consumer_preserves_all_channels_and_site_correlation():
    rows, child, _ = _upstream_rows(sites=("2", "1"))
    values = rows.upstream_child_measurement_values(child)
    for channel in ("1", "2", "5", "3"):
        feature = f"Intensity_MeanIntensity_Orig{channel}"
        for index in (0, 1):
            for label in (1, 2):
                assert (
                    values[index, label][feature]
                    == int(channel) * 100 + (index + 1) * 10 + label
                )


@pytest.mark.parametrize("kwargs", ({"well": "B01"}, {"time": "2"}, {"sites": ("3",)}))
def test_actual_upstream_consumer_rejects_incompatible_source_planes(kwargs):
    rows, child, _ = _upstream_rows(**kwargs)
    with pytest.raises(ValueError, match="does not align"):
        rows.upstream_child_measurement_values(child)


def test_actual_parent_means_include_each_channel_without_merging_site_ids():
    from openhcs.core.runtime_relationships import (
        ObjectRelationship,
        DirectedObjectRelationshipPayload,
        ObjectRelationshipDeclaration,
    )

    rows, child, contract = _upstream_rows(sites=("2", "1"))
    parent = contract.artifact_inputs.of_artifact_type(ObjectLabelsArtifactType)[0]
    spec = rows.request.spec
    relationship = ObjectRelationship.from_payload(
        name=spec.name,
        declaration=next(
            relation
            for relation in spec.relations
            if isinstance(relation, ObjectRelationshipDeclaration)
        ),
        payload=DirectedObjectRelationshipPayload(
            source_ids=(1, 1, 1, 1),
            target_ids=(1, 2, 1, 2),
            slice_indices=(0, 0, 1, 1),
            slice_count=2,
        ),
    )
    result = rows.parent_mean_upstream_measurement_rows(
        parent_spec=parent, child_spec=child, payload=relationship
    )
    actual = list(result.iter_row_mappings())
    assert len(actual) == 2
    for index, row in enumerate(actual):
        assert row["slice_index"] == index and row["object_label"] == 1
        for channel in ("1", "2", "5", "3"):
            assert (
                row[f"Mean_Children_Intensity_MeanIntensity_Orig{channel}"]
                == int(channel) * 100 + (index + 1) * 10 + 1.5
            )


def test_upstream_tables_without_source_coordinates_are_rejected():
    rows, child, _ = _upstream_rows()
    table = next(
        record.value.data
        for record in rows.request.adapter.request.context.runtime_value_store.values()
        if isinstance(record.value.data, MeasurementTable)
    )
    table.source_image_provenance_planes = SourceImageProvenancePlanes()
    with pytest.raises(ValueError, match="complete source image-set identity"):
        rows.upstream_child_measurement_values(child)


def test_input_relation_preserves_original_output_and_surviving_input_relations():
    from openhcs.core.artifacts import (
        InputObjectMeasurementSourceRelation,
        ArtifactSpecRelation,
    )

    _, child = _declared_input()

    class SharedSubjectDependency(ArtifactSpecRelation):
        target_plan_type = None

    relation = SharedSubjectDependency(child.ref())
    output = ArtifactSpec.output(
        "intensity",
        MeasurementsArtifactType,
        relations=(ObjectMeasurementSubjectRelation(child.ref()), relation),
    )
    identity = InputObjectMeasurementSourceRelation(child.ref())
    projected = identity.input_spec_for_output(output)
    assert output.plan_type is ArtifactOutputPlan
    assert output.relations == (ObjectMeasurementSubjectRelation(child.ref()), relation)
    assert projected.plan_type is ArtifactInputPlan
    assert projected.relations == (relation, identity)
    assert (
        projected.name == output.name
        and projected.artifact_type is output.artifact_type
    )


def test_measurement_input_relation_rejects_an_image_subject_and_nonmeasurement_target():
    from openhcs.core.artifacts import (
        InputObjectMeasurementSourceRelation,
        ImageArtifactType,
    )

    with pytest.raises(ValueError, match="object-labels source"):
        InputObjectMeasurementSourceRelation(
            ArtifactSpec.input("Image", ImageArtifactType).ref()
        )
    _, child = _declared_input()
    with pytest.raises(ValueError, match="target artifact type"):
        ArtifactSpec.input(
            "Image",
            ImageArtifactType,
            relations=(InputObjectMeasurementSourceRelation(child.ref()),),
        )


@pytest.mark.parametrize("dynamic", (False, True))
def test_plate_projection_keeps_complete_producer_scope(dynamic):
    from openhcs.core.callable_contract import FunctionStepExecutionScope
    from openhcs.core.artifacts import ArtifactInputProjectionPlan

    edge, _ = _compiled_edge(dynamic=dynamic, declared=False)
    scope = ArtifactInputProjectionPlan.producer_selection_for_invocation(
        input_spec=edge.spec,
        storage_plan=edge.storage_plan,
        component_scopes=(),
        consumer_variable_components=ComponentSet(),
        invocation_key=edge.key.invocation_key,
        execution_scope=FunctionStepExecutionScope.PLATE,
    )
    assert scope == edge.storage_plan.producer_group_scope()


def test_compiled_input_cannot_silently_narrow_complete_declaration():
    edge, _ = _compiled_edge()
    narrowed = replace(
        edge,
        projection=replace(
            edge.projection,
            producer_selection_scope=ComponentGroupScope.from_raw(
                ("3",), component=AllComponents.CHANNEL
            ),
        ),
    )
    with pytest.raises(ValueError, match="contradicts declaration"):
        _runtime_input(narrowed).records(_measurement_store(edge))


def test_complete_input_keeps_existing_record_scope_ambiguity_guard():
    edge, _ = _compiled_edge(dynamic=True)
    store = _measurement_store(edge, fixed=((AllComponents.SITE, "1"),))
    other = _measurement_store(edge, fixed=((AllComponents.SITE, "2"),))
    store.merge_observed_values(other.observed_values)
    with pytest.raises(RuntimeError, match="Ambiguous RuntimeValueStore records"):
        _runtime_input(edge).records(store)


def test_upstream_repeated_source_coordinates_do_not_merge_distinct_row_planes():
    rows, child, _ = _upstream_rows(sites=("1", "1"))
    with pytest.raises(ValueError, match="row axes .* exceed its source axis"):
        rows.upstream_child_measurement_values(child)


@pytest.mark.parametrize(
    "case", ("input-role", "image-kind", "other-object", "undeclared-subject")
)
def test_relation_refuses_producers_outside_its_measurement_subject(case):
    from openhcs.core.artifacts import (
        InputObjectMeasurementSourceRelation,
        ArtifactSpecRelation,
        ImageArtifactType,
    )

    _, child = _declared_input()
    subject = InputObjectMeasurementSourceRelation(child.ref())
    if case == "input-role":
        spec = ArtifactSpec.input("prior", MeasurementsArtifactType)
    elif case == "image-kind":
        spec = ArtifactSpec.output(
            "prior", ImageArtifactType, relations=(ArtifactSpecRelation(child.ref()),)
        )
    elif case == "other-object":
        other = ArtifactSpec.input("Others", ObjectLabelsArtifactType)
        spec = ArtifactSpec.output(
            "prior",
            MeasurementsArtifactType,
            relations=(ObjectMeasurementSubjectRelation(other.ref()),),
        )
    else:
        spec = ArtifactSpec.output("prior", MeasurementsArtifactType)
    assert not subject.matches_output(spec)
    with pytest.raises(ValueError, match="does not measure declared object source"):
        subject.input_spec_for_output(spec)


def test_relation_selection_conflicts_fail_without_last_writer_precedence():
    from openhcs.core.artifacts import ArtifactSpecRelation, ArtifactInputProjectionPlan

    edge, child = _compiled_edge()

    class SingleChannelRelation(ArtifactSpecRelation):
        target_plan_type = ArtifactInputPlan

        def input_producer_selection_scope(self, producer_scope):
            return ComponentGroupScope.from_raw(("1",), component=AllComponents.CHANNEL)

    spec = replace(
        edge.spec, relations=(*edge.spec.relations, SingleChannelRelation(child.ref()))
    )
    with pytest.raises(ValueError, match="conflicting producer selection scopes"):
        ArtifactInputProjectionPlan.declared_producer_selection_scope(
            spec, edge.storage_plan
        )


def test_complete_dynamic_input_rejects_foreign_producer_location():
    edge, _ = _compiled_edge(dynamic=True)
    foreign = RuntimeValueStore()
    for record in _measurement_store(edge).values():
        foreign.record(
            record.value,
            path=record.path.replace("/memory/", "/another-producer/"),
            backend=record.backend,
        )
    with pytest.raises(RuntimeError, match="Missing dynamic grouped artifact input"):
        _runtime_input(edge).records(foreign)


def test_complete_dynamic_input_rejects_foreign_producer_backend():
    edge, _ = _compiled_edge(dynamic=True)
    foreign = RuntimeValueStore()
    for record in _measurement_store(edge).values():
        foreign.record(record.value, path=record.path, backend="disk")
    with pytest.raises(RuntimeError, match="Missing dynamic grouped artifact input"):
        _runtime_input(edge).records(foreign)


def test_complete_dynamic_input_selects_compiled_producer_after_workspace_rebinding():
    edge, _ = _compiled_edge(dynamic=True)
    store = _measurement_store(edge)
    original = store.values()
    for record in original:
        store.replace(
            record.value,
            path=record.path.replace("/memory/", "/later-producer/"),
            backend=record.backend,
        )
    assert _runtime_input(edge).records(store) == original
