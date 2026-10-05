from dataclasses import replace
import pickle

import numpy as np
import pytest

from openhcs.constants.constants import AllComponents, get_multiprocessing_axis
from openhcs.core.artifacts import (
    ArtifactInputProjectionPlan,
    ArtifactInputPlan,
    ArtifactOutputPlan,
    ArtifactSpec,
    ImageArtifactType,
    InputGroupLineageSourceRelation,
    ObjectLabelsArtifactType,
    MeasurementsArtifactType,
)
from openhcs.core.function_patterns import (
    DEFAULT_GROUP_KEY,
    FunctionInvocationKey,
    InvocationArtifactInputEdgePlan,
    InvocationArtifactInputProjectionKey,
)
from openhcs.core.runtime_stores import (
    RuntimeArtifactAddress,
    RuntimeArtifactInput,
    RuntimeArtifactDynamicComponentTarget,
    RuntimeArtifactLocation,
    RuntimeArtifactLocationTarget,
    RuntimeArtifactQuery,
    RuntimeValueStore,
    StoredRuntimeValue,
)
from openhcs.core.component_group_scope import ComponentGroupScope
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.component_set import ComponentSet
from openhcs.core.callable_contract import CallableContract
from openhcs.core.runtime_equivalence import (
    RuntimeMeasurementObservationAxis,
)
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_data,
    image_payload_metadata,
)
from openhcs.core.measurement_row_materialization import (
    MeasurementProjectedColumnarRows,
    MeasurementSparseColumnarRows,
)
from openhcs.core.runtime_measurements import (
    MeasurementTable,
)
from openhcs.core.runtime_tabular_values import (
    FieldSpec,
)
from openhcs.core.runtime_measurements import (
    MeasurementScope,
    MeasurementSubject,
)
from openhcs.core.measurement_feature_queries import (
    RuntimeObjectLabelMeasurementQuery,
    RuntimeObjectLabelMeasurementQueryCache,
)
from openhcs.core.runtime_artifact_queries import RuntimeMeasurementTablesQueryCache
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
)
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.runtime_artifact_values import ArtifactKey, RuntimeValue
from openhcs.core.runtime_object_labels import ObjectLabelSet, ObjectLabelVariantData
from openhcs.core.source_bindings import (
    CompiledSourceBindingPlan,
    ComponentSelector,
    NamedSourceBinding,
)
from openhcs.core.source_matching import SourceImageSetIdentityCompatibility, SourceImageSetIdentityPolicy
from openhcs.interop.cellprofiler.runtime.artifact_binding import RuntimeInputBindingRequest
from tests.unit.cellprofiler_runtime_test_support import cellprofiler_runtime_adapter_for_test


def _runtime_input_edge(
    storage_plan: ArtifactInputPlan,
    *,
    invocation_scope: ComponentGroupScope,
    producer_selection_scope: ComponentGroupScope,
    component_scopes: tuple[ComponentGroupScope, ...],
    consumer_variable_components: tuple[AllComponents, ...],
) -> InvocationArtifactInputEdgePlan:
    invocation_key = FunctionInvocationKey(
        "runtime_input_test",
        DEFAULT_GROUP_KEY,
        0,
    )
    projection = ArtifactInputProjectionPlan(
        invocation_scope=invocation_scope,
        producer_selection_scope=producer_selection_scope,
        component_scopes=component_scopes,
        consumer_variable_components=consumer_variable_components,
    )
    return InvocationArtifactInputEdgePlan(
        key=InvocationArtifactInputProjectionKey(
            invocation_key=invocation_key,
            input_index=0,
        ),
        spec=ArtifactSpec.input(
            storage_plan.name,
            storage_plan.artifact_type,
            sidecar_role=storage_plan.sidecar_role,
        ),
        storage_plan=storage_plan,
        projection=projection,
    )


def _runtime_value(name="measurements", path="/memory/measurements.pkl"):
    return RuntimeValue.normalize(
        ArtifactOutputPlan(
            name=name,
            path=path,
            artifact_type=MeasurementsArtifactType,
            group_keys=("DAPI",),
            group_component=AllComponents.CHANNEL,
        ),
        MeasurementTable(
            name=name,
            rows=MeasurementSparseColumnarRows.from_rows(
                ({"object_id": 1},),
                fields=(FieldSpec("object_id", int),),
            ),
            subject=MeasurementSubject(
                MeasurementScope.ARTIFACT,
                name,
            ),
        ),
        axis_id="A01",
    )


def _label_query(feature_name="AreaShape_Area"):
    return RuntimeObjectLabelMeasurementQuery(
        axis_id="A01",
        group_key="DAPI",
        object_name="Cells",
        feature_name=feature_name,
        label_domain=(1,),
    )


@pytest.mark.parametrize("mutation", ("record", "replace", "clear", "merge"))
def test_store_mutations_invalidate_all_derived_query_domains(mutation):
    store = RuntimeValueStore()
    original = _runtime_value()
    store.record(original, path="/memory/measurements.pkl", backend="memory")
    label_cache = store.query_cache(RuntimeObjectLabelMeasurementQueryCache)
    tables_cache = store.query_cache(RuntimeMeasurementTablesQueryCache)
    query = _label_query()
    label_cache.store_value(query, (np.asarray([11.0]),))
    tables_cache.store_value(("A01", "DAPI"), (original.data,))

    if mutation == "record":
        store.record(_runtime_value("new"), path="/memory/new.pkl", backend="memory")
    elif mutation == "replace":
        store.replace(original, path="/memory/replacement.pkl", backend="memory")
    elif mutation == "clear":
        store.clear()
    else:
        worker = RuntimeValueStore()
        worker.record(
            _runtime_value("worker"), path="/memory/worker.pkl", backend="memory"
        )
        store.merge_observed_values(worker.observed_values)

    assert label_cache.cached_value(query) is None
    assert tables_cache.cached_value(("A01", "DAPI")) is None
    assert store.query_cache(RuntimeObjectLabelMeasurementQueryCache) is label_cache
    assert store.query_cache(RuntimeMeasurementTablesQueryCache) is tables_cache


def test_store_query_values_are_bounded_and_isolated_between_stores():
    first, second = RuntimeValueStore(), RuntimeValueStore()
    first_cache = first.query_cache(RuntimeObjectLabelMeasurementQueryCache)
    second_cache = second.query_cache(RuntimeObjectLabelMeasurementQueryCache)
    first_cache.max_entries = 2
    queries = tuple(_label_query(feature) for feature in ("a", "b", "c"))
    values = (np.asarray([42.0]),)
    first_cache.store_value(queries[0], values)
    first_cache.store_value(queries[1], values)
    assert first_cache.cached_value(queries[0]) is values
    first_cache.store_value(queries[2], values)

    assert first_cache.cached_value(queries[0]) is values
    assert first_cache.cached_value(queries[1]) is None
    assert first_cache.cached_value(queries[2]) is values
    assert second_cache.cached_value(queries[0]) is None


def test_store_transport_excludes_derived_caches_and_retains_records():
    store = RuntimeValueStore()
    value = _runtime_value()
    value.data.rows = MeasurementProjectedColumnarRows(
        {"object_id": (1,)}, fields=(FieldSpec("object_id", int),)
    )
    store.record(value, path="/memory/measurements.pkl", backend="memory")
    serialized_without_cache = pickle.dumps(store, protocol=5)
    query = _label_query()
    cache = store.query_cache(RuntimeObjectLabelMeasurementQueryCache)
    values = (np.ones(100_000),)
    cache.store_value(query, values)
    store.query_cache(RuntimeMeasurementTablesQueryCache).store_value(
        ("A01", "DAPI"), (value.data,)
    )

    assert pickle.dumps(store, protocol=5) == serialized_without_cache
    restored = pickle.loads(serialized_without_cache)
    assert restored.revision == store.revision
    assert len(restored) == len(store) == 1
    assert (
        restored.observed_values[0].data.row_mappings()
        == value.data.row_mappings()
    )
    assert (
        restored.query_cache(RuntimeObjectLabelMeasurementQueryCache).cached_value(
            query
        )
        is None
    )
    assert (
        restored.query_cache(RuntimeMeasurementTablesQueryCache).cached_value(
            ("A01", "DAPI")
        )
        is None
    )
    assert cache.cached_value(query) is values


def test_output_plan_uses_its_single_scope_for_ungrouped_invocation():
    output_plan = ArtifactOutputPlan(
        name="Nuclei",
        path="/memory/Nuclei.pkl",
        artifact_type=ObjectLabelsArtifactType,
        group_keys=("1",),
        group_component=AllComponents.CHANNEL,
        paths_by_group={"1": "/memory/Nuclei_1.pkl"},
    )

    resolved = output_plan.for_invocation_group(None)

    assert resolved.group_keys == ("1",)
    assert resolved.group_component is AllComponents.CHANNEL
    assert resolved.path == "/memory/Nuclei_1.pkl"


def test_ungrouped_output_plan_ignores_incidental_invocation_group():
    output_plan = ArtifactOutputPlan(
        name="RGBImage",
        path="/memory/RGBImage.pkl",
        artifact_type=ImageArtifactType,
        group_keys=(None,),
        group_component=None,
        paths_by_group={None: "/memory/RGBImage.pkl"},
    )

    resolved = output_plan.for_invocation_group("1")

    assert resolved.group_keys == (None,)
    assert resolved.group_component is None
    assert resolved.path == "/memory/RGBImage.pkl"


def test_runtime_artifact_address_round_trips_fixed_component_values():
    scope = RuntimeExecutionAxisScope.from_raw(
        "A01",
        component=AllComponents.CHANNEL,
        value="2",
        fixed_component_values=(
            (AllComponents.Z_INDEX, 3),
            (AllComponents.SITE, 1),
        ),
    )
    address = RuntimeArtifactAddress(
        key=ArtifactKey(
            name="measurements",
            artifact_type=MeasurementsArtifactType,
            scope=scope,
        ),
        location=RuntimeArtifactLocation(
            path="/memory/measurements.pkl",
            backend="memory",
        ),
        value_type="MeasurementTable",
    )

    restored = RuntimeArtifactAddress.from_dict(address.to_dict())

    assert restored == address
    assert restored.key.scope.fixed_component_values == scope.fixed_component_values


def test_runtime_artifact_key_canonicalizes_group_coordinate_value():
    numeric_scope = RuntimeExecutionAxisScope.from_raw(
        "A01",
        component=AllComponents.CHANNEL,
        value=2,
    )
    text_scope = RuntimeExecutionAxisScope.from_raw(
        "A01",
        component=AllComponents.CHANNEL,
        value="2",
    )

    numeric_key = ArtifactKey(
        name="measurements",
        artifact_type=MeasurementsArtifactType,
        scope=numeric_scope,
    )
    text_key = ArtifactKey(
        name="measurements",
        artifact_type=MeasurementsArtifactType,
        scope=text_scope,
    )

    assert numeric_scope == text_scope
    assert numeric_key == text_key
    assert hash(numeric_key) == hash(text_key)
    with pytest.raises(TypeError, match="value must be canonical text"):
        RuntimeExecutionAxisScope(
            axis_id="A01",
            component=AllComponents.CHANNEL,
            value=2,
        )


def test_dynamic_output_plan_requires_invocation_group():
    output_plan = ArtifactOutputPlan(
        name="ChannelImage",
        path="/memory/ChannelImage.pkl",
        artifact_type=ImageArtifactType,
        group_keys=(None,),
        group_component=AllComponents.CHANNEL,
        paths_by_group={None: "/memory/ChannelImage.pkl"},
    )

    with pytest.raises(ValueError, match="requires a concrete runtime key"):
        output_plan.for_invocation_group(None)


def test_runtime_value_store_records_and_finds_by_typed_identity():
    store = RuntimeValueStore()
    value = _runtime_value()

    record = store.record(
        value,
        path="/memory/measurements.pkl",
        backend="memory",
    )

    assert store.get(value.key) is record
    assert store.find(name="measurements") == (record,)
    assert store.find(
        name="measurements",
        artifact_type=MeasurementsArtifactType,
        axis_id="A01",
        group_key="DAPI",
        match_group=True,
    ) == (record,)
    assert store.find_by_location(
        path="/memory/measurements.pkl",
        backend="memory",
    ) == (record,)
    assert store.find(group_key="GFP", match_group=True) == ()


def test_runtime_value_store_keeps_fixed_component_artifacts_distinct() -> None:
    output_plan = ArtifactOutputPlan(
        name="measurements",
        path="/memory/measurements.pkl",
        artifact_type=MeasurementsArtifactType,
        group_keys=("2",),
        group_component=AllComponents.CHANNEL,
    ).for_group("2")
    store = RuntimeValueStore()
    records = []
    for z_index in ("1", "2"):
        execution_scope = RuntimeExecutionAxisScope.from_raw(
            "A01",
            component=AllComponents.CHANNEL,
            value="2",
            fixed_component_values=((AllComponents.Z_INDEX, z_index),),
        )
        value = RuntimeValue.normalize_for_execution_scope(
            output_plan,
            MeasurementTable(
                name="measurements",
                rows=MeasurementSparseColumnarRows.from_rows(
                    ({"z_index": z_index, "value": int(z_index)},),
                    fields=(
                        FieldSpec("z_index", str),
                        FieldSpec("value", int),
                    ),
                ),
                subject=MeasurementSubject(
                    MeasurementScope.ARTIFACT,
                    "measurements",
                ),
            ),
            execution_scope=execution_scope,
        )
        records.append(
            store.replace(
                value,
                path=output_plan.path,
                backend="memory",
            )
        )

    assert records[0].key != records[1].key
    assert store.values() == tuple(records)
    assert tuple(
        record.key.scope.value_text_for_component(AllComponents.Z_INDEX)
        for record in store.values()
    ) == ("1", "2")

    input_plan = ArtifactInputPlan(
        name="measurements",
        path=output_plan.path,
        artifact_type=MeasurementsArtifactType,
        group_keys=("2",),
        group_component=AllComponents.CHANNEL,
    )
    runtime_input = RuntimeArtifactInput(
        edge_plan=_runtime_input_edge(
            input_plan,
            invocation_scope=ComponentGroupScope.dynamic(AllComponents.CHANNEL),
            producer_selection_scope=input_plan.producer_group_scope(),
            component_scopes=(ComponentGroupScope.dynamic(AllComponents.CHANNEL),),
            consumer_variable_components=(),
        ),
        axis_scope=RuntimeExecutionAxisScope.from_raw(
            "A01",
            component=AllComponents.CHANNEL,
            value="2",
            fixed_component_values=((AllComponents.Z_INDEX, "2"),),
        ),
        backend="memory",
    )

    assert runtime_input.records(store) == (records[1],)


def test_runtime_value_empty_fixed_scope_preserves_ordinary_key_identity() -> None:
    output_plan = ArtifactOutputPlan(
        name="measurements",
        path="/memory/measurements.pkl",
        artifact_type=MeasurementsArtifactType,
        group_keys=("2",),
        group_component=AllComponents.CHANNEL,
    ).for_group("2")
    table = MeasurementTable(
        name="measurements",
        rows=MeasurementSparseColumnarRows.from_rows(
            ({"value": 1},),
            fields=(FieldSpec("value", int),),
        ),
        subject=MeasurementSubject(MeasurementScope.ARTIFACT, "measurements"),
    )

    ordinary = RuntimeValue.normalize(output_plan, table, axis_id="A01")
    exact_empty = RuntimeValue.normalize_for_execution_scope(
        output_plan,
        table,
        execution_scope=RuntimeExecutionAxisScope(axis_id="A01"),
    )

    assert exact_empty.key == ordinary.key
    assert exact_empty.key.scope.fixed_component_values == ()


def test_runtime_value_store_rejects_same_key_different_path():
    store = RuntimeValueStore()
    value = _runtime_value()
    store.record(value, path="/memory/measurements.pkl", backend="memory")

    with pytest.raises(ValueError, match="cannot overwrite"):
        store.record(value, path="/other/measurements.pkl", backend="memory")


def test_runtime_value_store_replace_updates_current_binding_and_keeps_locations():
    store = RuntimeValueStore()
    value = _runtime_value()
    original = store.record(value, path="/memory/measurements.pkl", backend="memory")

    replacement = store.replace(
        value,
        path="/other/measurements.pkl",
        backend="memory",
    )

    assert store.get(value.key) is replacement
    assert store.find_by_location(
        path="/memory/measurements.pkl",
        backend="memory",
    ) == (original,)
    assert store.find_by_location(
        path="/other/measurements.pkl",
        backend="memory",
    ) == (replacement,)


def test_runtime_value_store_find_matching_cache_invalidates_after_replace():
    store = RuntimeValueStore()
    value = _runtime_value()
    original = store.record(value, path="/memory/measurements.pkl", backend="memory")
    query = RuntimeArtifactQuery(
        name="measurements",
        artifact_type=MeasurementsArtifactType,
        axis_id="A01",
        target=RuntimeArtifactDynamicComponentTarget(
            ArtifactInputPlan(
                name="measurements",
                path="/memory/measurements.pkl",
                artifact_type=MeasurementsArtifactType,
                group_component=AllComponents.CHANNEL,
            ),
            "memory",
        ),
    )

    assert store.find_matching(query) == (original,)

    replacement = store.replace(
        value,
        path="/memory/measurements.pkl",
        backend="memory",
    )

    assert store.find_matching(query) == (replacement,)
    assert store.find_matching(query)[0] is replacement
    assert store.get(value.key) is replacement


def test_runtime_artifact_query_from_input_plan_uses_group_path():
    query = RuntimeArtifactQuery.from_input_plan(
        ArtifactInputPlan(
            name="DNA",
            path="/memory/DNA.pkl",
            artifact_type=ImageArtifactType,
            group_keys=("1", "2"),
            group_component=AllComponents.SITE,
            paths_by_group={"1": "/memory/DNA_s1.pkl", "2": "/memory/DNA_s2.pkl"},
        ),
        axis_id="A01",
        backend="memory",
        group_key="2",
    )

    assert isinstance(query.target, RuntimeArtifactLocationTarget)
    assert query.target.location.path == "/memory/DNA_s2.pkl"
    assert query.target.location.backend == "memory"


def test_runtime_artifact_query_from_dynamic_input_plan_matches_discovered_groups():
    query = RuntimeArtifactQuery.from_input_plan(
        ArtifactInputPlan(
            name="measurements",
            path="/memory/measurements.pkl",
            artifact_type=MeasurementsArtifactType,
            group_component=AllComponents.CHANNEL,
            paths_by_group={None: "/memory/measurements.pkl"},
        ),
        axis_id="A01",
        backend="memory",
    )

    assert isinstance(query.target, RuntimeArtifactDynamicComponentTarget)
    value = _runtime_value(path="/memory/measurements_wDAPI.pkl")
    assert query.matches(
        StoredRuntimeValue(
            key=value.key,
            data=value.data,
            materialization_source_metadata=value.materialization_source_metadata,
            location=RuntimeArtifactLocation(
                path="/memory/measurements_wDAPI.pkl",
                backend="memory",
            ),
        )
    )


def test_runtime_artifact_query_from_dynamic_output_plan_uses_runtime_group_path():
    query = RuntimeArtifactQuery.from_output_plan(
        ArtifactOutputPlan(
            name="RGBImage",
            path="/memory/A01_RGBImage.pkl",
            artifact_type=ImageArtifactType,
            group_component=AllComponents.SITE,
            paths_by_group={None: "/memory/A01_RGBImage.pkl"},
        ),
        axis_id="A01",
        backend="memory",
        group_key="3",
    )

    assert isinstance(query.target, RuntimeArtifactLocationTarget)
    assert query.target.location.path == "/memory/A01_w3_RGBImage.pkl"
    assert query.target.location.backend == "memory"


def test_runtime_artifact_input_projection_selects_same_component_group():
    store = RuntimeValueStore()
    paths = {
        "1": "/memory/image_site_1.pkl",
        "2": "/memory/image_site_2.pkl",
    }
    output_plan = ArtifactOutputPlan(
        name="image",
        path="/memory/image.pkl",
        artifact_type=ImageArtifactType,
        group_keys=("1", "2"),
        group_component=AllComponents.SITE,
        paths_by_group=paths,
    )
    for group_key, value in (("1", 1.0), ("2", 2.0)):
        group_plan = output_plan.for_group(group_key)
        store.record(
            RuntimeValue.normalize(
                group_plan,
                np.full((2, 2), value, dtype=np.float32),
                axis_id="A01",
            ),
            path=group_plan.path,
            backend="memory",
        )

    storage_plan = ArtifactInputPlan(
        name="image",
        path="/memory/image.pkl",
        artifact_type=ImageArtifactType,
        group_keys=("1", "2"),
        group_component=AllComponents.SITE,
        paths_by_group=paths,
    )
    records = RuntimeArtifactInput(
        edge_plan=_runtime_input_edge(
            storage_plan,
            invocation_scope=ComponentGroupScope.dynamic(AllComponents.SITE),
            producer_selection_scope=ComponentGroupScope.dynamic(AllComponents.SITE),
            component_scopes=(ComponentGroupScope.dynamic(AllComponents.SITE),),
            consumer_variable_components=(AllComponents.CHANNEL,),
        ),
        axis_scope=RuntimeExecutionAxisScope.from_raw(
            "A01",
            component=AllComponents.SITE,
            value="2",
        ),
        backend="memory",
    ).records(store)

    assert tuple(record.key.scope.value_text for record in records) == ("2",)


def test_runtime_artifact_input_collects_exact_complete_producer_scope():
    store = RuntimeValueStore()
    paths = {
        "1": "/memory/measurements_channel_1.pkl",
        "2": "/memory/measurements_channel_2.pkl",
    }
    output_plan = ArtifactOutputPlan(
        name="measurements",
        path="/memory/measurements.pkl",
        artifact_type=MeasurementsArtifactType,
        group_keys=("1", "2"),
        group_component=AllComponents.CHANNEL,
        paths_by_group=paths,
    )
    for group_key in ("1", "2"):
        group_plan = output_plan.for_group(group_key)
        store.record(
            RuntimeValue.normalize(
                group_plan,
                MeasurementTable(
                    name="measurements",
                    rows=MeasurementSparseColumnarRows.from_rows(
                        ({"value": float(group_key)},),
                        fields=(FieldSpec("value", float),),
                    ),
                    subject=MeasurementSubject(MeasurementScope.IMAGE, "Image"),
                ),
                axis_id="A01",
            ),
            path=group_plan.path,
            backend="memory",
        )

    storage_plan = ArtifactInputPlan(
        name="measurements",
        path="/memory/measurements.pkl",
        artifact_type=MeasurementsArtifactType,
        group_keys=("1", "2"),
        group_component=AllComponents.CHANNEL,
        paths_by_group=paths,
    )
    runtime_input = RuntimeArtifactInput(
        edge_plan=_runtime_input_edge(
            storage_plan,
            invocation_scope=ComponentGroupScope(
                ("1",),
                component=AllComponents.CHANNEL,
            ),
            producer_selection_scope=storage_plan.producer_group_scope(),
            component_scopes=(),
            consumer_variable_components=(AllComponents.SITE,),
        ),
        axis_scope=RuntimeExecutionAxisScope.from_raw(
            "A01",
            component=AllComponents.CHANNEL,
            value="1",
        ),
        backend="memory",
    )
    records = runtime_input.records(store)

    assert tuple(record.key.scope.value_text for record in records) == ("1", "2")
    composed = runtime_input.composed_value(records)
    assert isinstance(composed, MeasurementTable)
    assert composed.name == "measurements"
    assert composed.subject == MeasurementSubject(MeasurementScope.IMAGE, "Image")
    assert tuple(composed.rows.column_values("value")) == (1.0, 2.0)


def test_runtime_artifact_input_projection_collects_variable_component_groups():
    store = RuntimeValueStore()
    output_plan = ArtifactOutputPlan(
        name="RGBImage",
        path="/memory/RGBImage.pkl",
        artifact_type=ImageArtifactType,
        group_component=AllComponents.SITE,
        paths_by_group={None: "/memory/RGBImage.pkl"},
    )
    for group_key, value in (("1", 1.0), ("2", 2.0)):
        group_plan = output_plan.for_group(group_key)
        store.record(
            RuntimeValue.normalize(
                group_plan,
                np.full((2, 2), value, dtype=np.float32),
                axis_id="A01",
            ),
            path=group_plan.path,
            backend="memory",
        )

    input_plan = ArtifactInputPlan(
        name="RGBImage",
        path="/memory/RGBImage.pkl",
        artifact_type=ImageArtifactType,
        group_component=AllComponents.SITE,
        paths_by_group={None: "/memory/RGBImage.pkl"},
    )
    runtime_input = RuntimeArtifactInput(
        edge_plan=_runtime_input_edge(
            input_plan,
            invocation_scope=ComponentGroupScope.dynamic(AllComponents.CHANNEL),
            producer_selection_scope=input_plan.producer_group_scope(),
            component_scopes=(ComponentGroupScope.dynamic(AllComponents.CHANNEL),),
            consumer_variable_components=(AllComponents.SITE,),
        ),
        axis_scope=RuntimeExecutionAxisScope.from_raw(
            "A01",
            component=AllComponents.CHANNEL,
            value="1",
        ),
        backend="memory",
    )
    records = runtime_input.records(store)
    payload = runtime_input.composed_value(records)

    assert tuple(record.key.scope.value_text for record in records) == ("1", "2")
    np.testing.assert_array_equal(
        payload,
        np.stack(
            (
                np.full((2, 2), 1.0, dtype=np.float32),
                np.full((2, 2), 2.0, dtype=np.float32),
            )
        ),
    )


def test_runtime_artifact_input_projection_transposes_producer_stack_axis() -> None:
    store = RuntimeValueStore()
    paths = {
        channel: f"/memory/image_channel_{channel}.pkl" for channel in ("1", "2", "3")
    }
    output_plan = ArtifactOutputPlan(
        name="image",
        path="/memory/image.pkl",
        artifact_type=ImageArtifactType,
        group_keys=("1", "2", "3"),
        group_component=AllComponents.CHANNEL,
        variable_components=(AllComponents.SITE,),
        paths_by_group=paths,
    )
    for channel_index, channel in enumerate(("1", "2", "3"), start=1):
        group_plan = output_plan.for_group(channel)
        payload = ImagePayloadMetadata(
            plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
            source_image_provenance_planes=(
                SourceImageProvenancePlanes.from_components(
                    paths=tuple(f"/source/site_{site}.tif" for site in (1, 2, 3)),
                    component_metadata=tuple(
                        {"site": str(site), "channel": channel} for site in (1, 2, 3)
                    ),
                )
            ),
        ).payload_with(
            np.stack(
                tuple(
                    np.full((2, 2), channel_index * 10 + site, dtype=np.float32)
                    for site in (1, 2, 3)
                )
            ),
            None,
        )
        store.record(
            RuntimeValue.normalize_for_execution_scope(
                group_plan,
                payload,
                execution_scope=RuntimeExecutionAxisScope.from_raw(
                    "A01", component=AllComponents.CHANNEL, value=channel,
                ),
            ),
            path=group_plan.path,
            backend="memory",
        )

    storage_plan = ArtifactInputPlan(
        name="image",
        path="/memory/image.pkl",
        artifact_type=ImageArtifactType,
        group_keys=("1", "2", "3"),
        group_component=AllComponents.CHANNEL,
        variable_components=(AllComponents.SITE,),
        paths_by_group=paths,
    )
    runtime_input = RuntimeArtifactInput(
        edge_plan=_runtime_input_edge(
            storage_plan,
            invocation_scope=ComponentGroupScope.dynamic(AllComponents.SITE),
            producer_selection_scope=storage_plan.producer_group_scope(),
            component_scopes=(ComponentGroupScope.dynamic(AllComponents.SITE),),
            consumer_variable_components=(AllComponents.CHANNEL,),
        ),
        axis_scope=RuntimeExecutionAxisScope.from_raw(
            "A01",
            component=AllComponents.SITE,
            value="2",
        ),
        backend="memory",
    )

    candidates = runtime_input.candidate_execution_scopes(
        store,
        ComponentGroupScope.dynamic(AllComponents.SITE),
        variable_components=ComponentSet((AllComponents.CHANNEL,)),
    )
    assert tuple(scope.value_text for scope in candidates) == ("1", "2", "3")
    assert all(scope.fixed_component_values == () for scope in candidates)

    payload = runtime_input.composed_value(runtime_input.records(store))

    np.testing.assert_array_equal(
        image_payload_data(payload),
        np.stack(
            tuple(
                np.full((2, 2), channel * 10 + 2, dtype=np.float32)
                for channel in (1, 2, 3)
            )
        ),
    )


def test_artifact_candidate_scopes_preserve_projected_site_time_correlation() -> None:
    path = "/memory/processed_pixels.pkl"
    variables = (AllComponents.SITE, AllComponents.TIMEPOINT)
    output_plan = ArtifactOutputPlan(
        name="image", path=path, artifact_type=ImageArtifactType,
        variable_components=variables,
    )
    storage_plan = ArtifactInputPlan(
        name="image", path=path, artifact_type=ImageArtifactType,
        variable_components=variables,
    )
    payload = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/source/original_first.tif", "/source/original_second.tif"),
            component_metadata=(
                {"site": "1", "timepoint": "3"},
                {"site": "2", "timepoint": "4"},
            ),
        ),
    ).payload_with(
        np.stack((np.full((2, 2), 17.0), np.full((2, 2), 29.0))),
        np.asarray([[[True, False], [False, True]], [[False, True], [True, False]]]),
    )
    store = RuntimeValueStore()
    store.record(RuntimeValue.normalize(output_plan, payload, axis_id="A01"),
                 path=path, backend="memory")
    edge = _runtime_input_edge(
        storage_plan,
        invocation_scope=ComponentGroupScope.dynamic(AllComponents.SITE),
        producer_selection_scope=ComponentGroupScope.ungrouped(),
        component_scopes=(
            ComponentGroupScope.dynamic(AllComponents.SITE),
            ComponentGroupScope.from_raw(("3",), component=AllComponents.TIMEPOINT),
        ),
        consumer_variable_components=(),
    )
    runtime_input = RuntimeArtifactInput(
        edge_plan=edge, backend="memory",
        axis_scope=RuntimeExecutionAxisScope.from_raw("A01", component=None, value=None),
    )
    candidates = runtime_input.candidate_execution_scopes(
        store, ComponentGroupScope.dynamic(AllComponents.SITE),
        variable_components=ComponentSet(),
    )
    (coordinates,) = tuple(candidates)
    assert coordinates.value_text == "1"
    assert coordinates.fixed_component_values == ((AllComponents.TIMEPOINT, "3"),)
    assert candidates[coordinates] == path
    selected = replace(runtime_input, axis_scope=coordinates).resolve_value(store)
    np.testing.assert_array_equal(image_payload_data(selected), np.full((2, 2), 17.0))
    np.testing.assert_array_equal(selected.mask, payload.mask[0])


def test_artifact_candidate_scopes_keep_actual_producer_group_as_fixed_context() -> None:
    path = "/memory/produced_pixels.pkl"
    output_plan = ArtifactOutputPlan(
        name="image", path=path, artifact_type=ImageArtifactType,
        group_component=AllComponents.CHANNEL, group_keys=("1",),
    )
    storage_plan = ArtifactInputPlan(
        name="image", path=path, artifact_type=ImageArtifactType,
        group_component=AllComponents.CHANNEL, group_keys=("1",),
    )
    payload = ImagePayloadMetadata(
        source_path="/source/old_filename_w9.tif",
        source_component_metadata={"site": "2", "timepoint": "3", "channel": "1", "z_index": "1"},
    ).payload_with(np.full((2, 2), 17.0), None)
    store = RuntimeValueStore()
    record = store.record(
        RuntimeValue.normalize_for_execution_scope(
            output_plan, payload,
            execution_scope=RuntimeExecutionAxisScope.from_raw(
                "A01", component=AllComponents.CHANNEL, value="1",
                fixed_component_values=((AllComponents.SITE, "2"), (AllComponents.TIMEPOINT, "3"), (AllComponents.Z_INDEX, "1")),
            ),
        ),
        path=path, backend="memory",
    )
    runtime_input = RuntimeArtifactInput(
        edge_plan=_runtime_input_edge(
            storage_plan,
            invocation_scope=ComponentGroupScope.dynamic(AllComponents.SITE),
            producer_selection_scope=storage_plan.producer_group_scope(),
            component_scopes=(ComponentGroupScope.dynamic(AllComponents.SITE),),
            consumer_variable_components=(),
        ),
        axis_scope=RuntimeExecutionAxisScope.from_raw("A01", component=None, value=None),
        backend="memory",
    )
    candidates = runtime_input.candidate_execution_scopes(
        store, ComponentGroupScope.dynamic(AllComponents.SITE),
        variable_components=ComponentSet(),
    )
    (coordinates,) = tuple(candidates)
    assert coordinates.value_text == "2"
    assert dict(coordinates.fixed_component_values) == {
        AllComponents.CHANNEL: "1", AllComponents.TIMEPOINT: "3", AllComponents.Z_INDEX: "1",
    }
    selected = replace(runtime_input, axis_scope=coordinates).records(store)
    assert len(selected) == 1
    assert selected[0] is record

    second_payload = ImagePayloadMetadata(
        source_path="/source/another_original.tif",
        source_component_metadata={"site": "2", "timepoint": "3", "channel": "1", "z_index": "2"},
    ).payload_with(np.full((2, 2), 29.0), None)
    second_record = store.record(
        RuntimeValue.normalize_for_execution_scope(
            output_plan, second_payload,
            execution_scope=RuntimeExecutionAxisScope.from_raw(
                "A01", component=AllComponents.CHANNEL, value="1",
                fixed_component_values=((AllComponents.SITE, "2"), (AllComponents.TIMEPOINT, "3"), (AllComponents.Z_INDEX, "2")),
            ),
        ),
        path=path, backend="memory",
    )
    candidates = runtime_input.candidate_execution_scopes(
        store, ComponentGroupScope.dynamic(AllComponents.SITE),
        variable_components=ComponentSet(),
    )
    assert len(candidates) == 2
    selected_records = tuple(
        replace(runtime_input, axis_scope=scope).records(store)
        for scope in candidates
    )
    assert selected_records == ((record,), (second_record,))


def test_runtime_artifact_input_projection_ignores_scalar_pixel_contributors() -> None:
    path = "/memory/scalar_image.pkl"
    output_plan = ArtifactOutputPlan(
        name="image",
        path=path,
        artifact_type=ImageArtifactType,
        variable_components=(AllComponents.SITE,),
    )
    storage_plan = ArtifactInputPlan(
        name="image",
        path=path,
        artifact_type=ImageArtifactType,
        variable_components=(AllComponents.SITE,),
    )
    runtime_input = RuntimeArtifactInput(
        edge_plan=_runtime_input_edge(
            storage_plan,
            invocation_scope=ComponentGroupScope.dynamic(AllComponents.SITE),
            producer_selection_scope=ComponentGroupScope.ungrouped(),
            component_scopes=(ComponentGroupScope.dynamic(AllComponents.SITE),),
            consumer_variable_components=(),
        ),
        axis_scope=RuntimeExecutionAxisScope.from_raw(
            "A01",
            component=AllComponents.SITE,
            value="2",
        ),
        backend="memory",
    )
    runtime_planes = SourceImageProvenancePlanes.from_components(
        paths=("/source/site_1.tif", "/source/site_2.tif"),
        component_metadata=({"site": "1"}, {"site": "2"}),
    )

    scalar_store = RuntimeValueStore()
    scalar_payload = ImagePayloadMetadata(
        source_component_metadata={"site": "2"},
        source_image_provenance_planes=runtime_planes.as_contributors(),
    ).payload_with(np.full((2, 2), 20, dtype=np.float32), None)
    scalar_store.record(
        RuntimeValue.normalize(output_plan, scalar_payload, axis_id="A01"),
        path=path,
        backend="memory",
    )

    resolved_scalar = runtime_input.resolve_value(scalar_store)

    np.testing.assert_array_equal(
        image_payload_data(resolved_scalar),
        np.full((2, 2), 20, dtype=np.float32),
    )
    scalar_planes = image_payload_metadata(
        resolved_scalar
    ).source_image_provenance_planes
    assert scalar_planes.runtime_component_metadata == ()
    assert scalar_planes.contributor_count == 2

    stacked_store = RuntimeValueStore()
    stacked_payload = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_provenance_planes=runtime_planes,
    ).payload_with(
        np.stack(
            (
                np.full((2, 2), 10, dtype=np.float32),
                np.full((2, 2), 20, dtype=np.float32),
            )
        ),
        None,
    )
    stacked_store.record(
        RuntimeValue.normalize(output_plan, stacked_payload, axis_id="A01"),
        path=path,
        backend="memory",
    )

    resolved_runtime_plane = runtime_input.resolve_value(stacked_store)

    np.testing.assert_array_equal(
        image_payload_data(resolved_runtime_plane),
        np.full((2, 2), 20, dtype=np.float32),
    )
    assert (
        runtime_planes.runtime_component_metadata == runtime_planes.component_metadata
    )


def test_runtime_artifact_input_projection_collapses_excluded_singleton_axis() -> None:
    store = RuntimeValueStore()
    paths = {site: f"/memory/image_site_{site}.pkl" for site in ("1", "2")}
    output_plan = ArtifactOutputPlan(
        name="image",
        path="/memory/image.pkl",
        artifact_type=ImageArtifactType,
        group_keys=("1", "2"),
        group_component=AllComponents.SITE,
        variable_components=(AllComponents.CHANNEL,),
        paths_by_group=paths,
    )
    for site_index, site in enumerate(("1", "2"), start=1):
        group_plan = output_plan.for_group(site)
        payload = ImagePayloadMetadata(
            plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
            source_image_provenance_planes=(
                SourceImageProvenancePlanes.from_components(
                    paths=(f"/source/site_{site}.tif",),
                    component_metadata=({"site": site, "channel": "1"},),
                )
            ),
        ).payload_with(np.full((1, 2, 2), site_index, dtype=np.float32), None)
        store.record(
            RuntimeValue.normalize(group_plan, payload, axis_id="A01"),
            path=group_plan.path,
            backend="memory",
        )

    storage_plan = ArtifactInputPlan(
        name="image",
        path="/memory/image.pkl",
        artifact_type=ImageArtifactType,
        group_keys=("1", "2"),
        group_component=AllComponents.SITE,
        variable_components=(AllComponents.CHANNEL,),
        paths_by_group=paths,
    )
    runtime_input = RuntimeArtifactInput(
        edge_plan=_runtime_input_edge(
            storage_plan,
            invocation_scope=ComponentGroupScope.dynamic(AllComponents.CHANNEL),
            producer_selection_scope=storage_plan.producer_group_scope(),
            component_scopes=(
                ComponentGroupScope(
                    ("1",),
                    component=AllComponents.CHANNEL,
                ),
            ),
            consumer_variable_components=(AllComponents.SITE,),
        ),
        axis_scope=RuntimeExecutionAxisScope.from_raw(
            "A01",
            component=AllComponents.CHANNEL,
            value="1",
        ),
        backend="memory",
    )

    projected_values = runtime_input.projected_values(store)
    assert all(type(value) is RuntimeValue for value in projected_values)
    assert all(image_payload_data(value.data).shape == (2, 2) for value in projected_values)
    assert all(image_payload_data(record.data).shape == (1, 2, 2) for record in store.values())
    payload = runtime_input.resolve_value(store)

    assert image_payload_data(payload).shape == (2, 2, 2)
    np.testing.assert_array_equal(
        image_payload_data(payload),
        np.stack(
            (
                np.full((2, 2), 1, dtype=np.float32),
                np.full((2, 2), 2, dtype=np.float32),
            )
        ),
    )
    assert image_payload_metadata(payload).plane_axis is RuntimePlaneAxis.RUNTIME_SLICE


def test_runtime_artifact_input_reconstructs_singleton_producer_group_axis() -> None:
    path = "/memory/image_site_1.pkl"
    output_plan = ArtifactOutputPlan(
        name="image",
        path=path,
        artifact_type=ImageArtifactType,
        group_keys=("1",),
        group_component=AllComponents.SITE,
        paths_by_group={"1": path},
    )
    store = RuntimeValueStore()
    store.record(
        RuntimeValue.normalize(
            output_plan.for_group("1"),
            np.full((2, 2), 1, dtype=np.float32),
            axis_id="A01",
        ),
        path=path,
        backend="memory",
    )
    storage_plan = ArtifactInputPlan(
        name="image",
        path=path,
        artifact_type=ImageArtifactType,
        group_keys=("1",),
        group_component=AllComponents.SITE,
        paths_by_group={"1": path},
    )
    runtime_input = RuntimeArtifactInput(
        edge_plan=_runtime_input_edge(
            storage_plan,
            invocation_scope=ComponentGroupScope.dynamic(AllComponents.CHANNEL),
            producer_selection_scope=storage_plan.producer_group_scope(),
            component_scopes=(ComponentGroupScope.dynamic(AllComponents.CHANNEL),),
            consumer_variable_components=(AllComponents.SITE,),
        ),
        axis_scope=RuntimeExecutionAxisScope.from_raw(
            "A01",
            component=AllComponents.CHANNEL,
            value="1",
        ),
        backend="memory",
    )

    payload = runtime_input.resolve_value(store)

    assert image_payload_data(payload).shape == (1, 2, 2)
    np.testing.assert_array_equal(
        image_payload_data(payload),
        np.full((1, 2, 2), 1, dtype=np.float32),
    )
    assert image_payload_metadata(payload).plane_axis is RuntimePlaneAxis.RUNTIME_SLICE


def test_runtime_artifact_input_keeps_singleton_scalar_selection_unstacked() -> None:
    path = "/memory/image_channel_1.pkl"
    output_plan = ArtifactOutputPlan(
        name="image",
        path=path,
        artifact_type=ImageArtifactType,
        group_keys=("1",),
        group_component=AllComponents.CHANNEL,
        paths_by_group={"1": path},
    )
    store = RuntimeValueStore()
    store.record(
        RuntimeValue.normalize(
            output_plan.for_group("1"),
            np.full((2, 2), 1, dtype=np.float32),
            axis_id="A01",
        ),
        path=path,
        backend="memory",
    )
    storage_plan = ArtifactInputPlan(
        name="image",
        path=path,
        artifact_type=ImageArtifactType,
        group_keys=("1",),
        group_component=AllComponents.CHANNEL,
        paths_by_group={"1": path},
    )
    runtime_input = RuntimeArtifactInput(
        edge_plan=_runtime_input_edge(
            storage_plan,
            invocation_scope=ComponentGroupScope.ungrouped(),
            producer_selection_scope=storage_plan.producer_group_scope(),
            component_scopes=(
                ComponentGroupScope(("1",), component=AllComponents.CHANNEL),
            ),
            consumer_variable_components=(AllComponents.SITE,),
        ),
        axis_scope=RuntimeExecutionAxisScope.from_raw(
            "A01",
            component=None,
            value=None,
        ),
        backend="memory",
    )

    payload = runtime_input.resolve_value(store)

    assert image_payload_data(payload).shape == (2, 2)
    assert image_payload_metadata(payload).plane_axis is None


def test_runtime_artifact_input_projection_selects_compiler_owned_group_for_ungrouped_invocation():
    storage_plan = ArtifactInputPlan(
        name="image",
        path="/memory/image.pkl",
        artifact_type=ImageArtifactType,
        group_keys=("1", "2"),
        group_component=AllComponents.CHANNEL,
    )
    runtime_input = RuntimeArtifactInput(
        edge_plan=_runtime_input_edge(
            storage_plan,
            invocation_scope=ComponentGroupScope.ungrouped(),
            producer_selection_scope=ComponentGroupScope(
                ("2",),
                component=AllComponents.CHANNEL,
            ),
            component_scopes=(
                ComponentGroupScope(
                    ("2",),
                    component=AllComponents.CHANNEL,
                ),
            ),
            consumer_variable_components=(AllComponents.SITE,),
        ),
        axis_scope=RuntimeExecutionAxisScope.from_raw(
            "A01",
            component=None,
            value=None,
        ),
        backend="memory",
    )

    assert (
        runtime_input.edge_plan.projection.producer_selection_scope
        == ComponentGroupScope(
            ("2",),
            component=AllComponents.CHANNEL,
        )
    )


def test_runtime_artifact_input_projection_keeps_equal_keys_component_typed():
    store = RuntimeValueStore()
    for component, path, value in (
        (AllComponents.SITE, "/memory/site_image.pkl", 1.0),
        (AllComponents.CHANNEL, "/memory/channel_image.pkl", 2.0),
    ):
        plan = ArtifactOutputPlan(
            name="image",
            path=path,
            artifact_type=ImageArtifactType,
            group_keys=("1",),
            group_component=component,
            paths_by_group={"1": path},
        )
        store.record(
            RuntimeValue.normalize(
                plan,
                np.full((2, 2), value, dtype=np.float32),
                axis_id="A01",
            ),
            path=path,
            backend="memory",
        )

    storage_plan = ArtifactInputPlan(
        name="image",
        path="/memory/site_image.pkl",
        artifact_type=ImageArtifactType,
        group_keys=("1",),
        group_component=AllComponents.SITE,
        paths_by_group={"1": "/memory/site_image.pkl"},
    )
    records = RuntimeArtifactInput(
        edge_plan=_runtime_input_edge(
            storage_plan,
            invocation_scope=ComponentGroupScope.dynamic(AllComponents.CHANNEL),
            producer_selection_scope=storage_plan.producer_group_scope(),
            component_scopes=(ComponentGroupScope.dynamic(AllComponents.CHANNEL),),
            consumer_variable_components=(AllComponents.SITE,),
        ),
        axis_scope=RuntimeExecutionAxisScope.from_raw(
            "A01",
            component=AllComponents.CHANNEL,
            value="1",
        ),
        backend="memory",
    ).records(store)

    assert len(records) == 1
    assert records[0].key.scope.component is AllComponents.SITE
    np.testing.assert_array_equal(records[0].data, np.full((2, 2), 1.0))


def test_runtime_artifact_input_projection_uses_compiled_group_for_plane_scope():
    store = RuntimeValueStore()
    path = "/memory/rgb_channel_3.pkl"
    output_plan = ArtifactOutputPlan(
        name="RGBImage",
        path=path,
        artifact_type=ImageArtifactType,
        group_keys=("3",),
        group_component=AllComponents.CHANNEL,
        paths_by_group={"3": path},
    )
    payload = ImagePayloadMetadata(
        source_component_metadata={"channel": "3"},
    ).payload_with(np.full((2, 2), 3.0, dtype=np.float32), None)
    store.record(
        RuntimeValue.normalize(output_plan.for_group("3"), payload, axis_id="A01"),
        path=path,
        backend="memory",
    )
    storage_plan = ArtifactInputPlan(
        name="RGBImage",
        path=path,
        artifact_type=ImageArtifactType,
        group_keys=("3",),
        group_component=AllComponents.CHANNEL,
        paths_by_group={"3": path},
    )
    runtime_input = RuntimeArtifactInput(
        edge_plan=_runtime_input_edge(
            storage_plan,
            invocation_scope=ComponentGroupScope.ungrouped(),
            producer_selection_scope=ComponentGroupScope(
                ("3",),
                component=AllComponents.CHANNEL,
            ),
            component_scopes=(
                ComponentGroupScope(
                    ("3",),
                    component=AllComponents.CHANNEL,
                ),
            ),
            consumer_variable_components=(AllComponents.SITE,),
        ),
        axis_scope=RuntimeExecutionAxisScope.from_raw(
            "A01",
            component=None,
            value=None,
        ),
        backend="memory",
    )

    assert (
        runtime_input.edge_plan.projection.producer_selection_scope
        == ComponentGroupScope(
            ("3",),
            component=AllComponents.CHANNEL,
        )
    )
    resolved = runtime_input.resolve_value(store)

    np.testing.assert_array_equal(
        image_payload_data(resolved), image_payload_data(payload)
    )


def test_runtime_value_store_observation_cursor_returns_delta_only():
    store = RuntimeValueStore()
    first_value = _runtime_value(name="first", path="/memory/first.pkl")
    first_record = store.record(
        first_value,
        path="/memory/first.pkl",
        backend="memory",
    )
    cursor = store.observation_cursor()
    second_value = _runtime_value(name="second", path="/memory/second.pkl")
    second_record = store.record(
        second_value,
        path="/memory/second.pkl",
        backend="memory",
    )

    assert store.observed_values_after(cursor) == (second_record,)
    assert store.observed_values == (first_record, second_record)


def test_runtime_value_store_observation_cursor_rejects_invalid_index():
    store = RuntimeValueStore()

    with pytest.raises(ValueError, match="beyond the current observation stream"):
        store.observed_values_after(
            store.observation_cursor().__class__(index=1, revision=0)
        )


def test_runtime_value_store_preserves_same_artifact_measurement_subjects():
    store = RuntimeValueStore()
    output_plan = ArtifactOutputPlan(
        name="RelateObjects_measurements",
        path="/memory/RelateObjects_measurements.pkl",
        artifact_type=MeasurementsArtifactType,
    )
    parent_value = RuntimeValue.normalize(
        output_plan,
        MeasurementTable(
            name="RelateObjects_measurements",
            rows=MeasurementSparseColumnarRows.from_rows(
                ({"object_label": 1, "children_count": 2},),
                fields=(
                    FieldSpec("object_label", int),
                    FieldSpec("children_count", int),
                ),
            ),
            subject=MeasurementSubject(MeasurementScope.OBJECT, "ParentObjects"),
        ),
        axis_id="A01",
    )
    child_value = RuntimeValue.normalize(
        output_plan,
        MeasurementTable(
            name="RelateObjects_measurements",
            rows=MeasurementSparseColumnarRows.from_rows(
                ({"object_label": 1, "parent_id": 1},),
                fields=(
                    FieldSpec("object_label", int),
                    FieldSpec("parent_id", int),
                ),
            ),
            subject=MeasurementSubject(MeasurementScope.OBJECT, "ChildObjects"),
        ),
        axis_id="A01",
    )

    parent_record = store.replace(
        parent_value,
        path="/memory/RelateObjects_measurements.pkl",
        backend="memory",
    )
    child_record = store.replace(
        child_value,
        path="/memory/RelateObjects_measurements.pkl",
        backend="memory",
    )

    assert parent_value.key != child_value.key
    assert store.find(
        name="RelateObjects_measurements",
        artifact_type=MeasurementsArtifactType,
        axis_id="A01",
    ) == (parent_record, child_record)


def test_runtime_value_store_preserves_same_subject_measurement_sources():
    store = RuntimeValueStore()
    name = "MeasureObjectIntensityDistribution_16_measurements"
    path = f"/memory/{name}.pkl"
    output_plan = ArtifactOutputPlan(
        name=name,
        path=path,
        artifact_type=MeasurementsArtifactType,
    )
    subject = MeasurementSubject(MeasurementScope.OBJECT, "Cells")
    records = []
    for source_image_name in ("Syto", "OrigSyto"):
        value = RuntimeValue.normalize(
            output_plan,
            MeasurementTable(
                name=name,
                rows=MeasurementSparseColumnarRows.from_rows(
                    ({"object_label": 1, "radial_fraction": 0.5},),
                    fields=(
                        FieldSpec("object_label", int),
                        FieldSpec("radial_fraction", float),
                    ),
                ),
                source_image_name=source_image_name,
                subject=subject,
            ),
            axis_id="A01",
        )
        records.append(
            store.replace(
                value,
                path=path,
                backend="memory",
            )
        )

    assert records[0].key != records[1].key
    assert store.find(
        name=name,
        artifact_type=MeasurementsArtifactType,
        axis_id="A01",
    ) == tuple(records)


def _same_location_measurement_subject_records() -> tuple[
    RuntimeValueStore,
    ArtifactInputPlan,
    dict[str, StoredRuntimeValue],
]:
    name = "MeasureObjectIntensity_6_measurements"
    path = f"/memory/{name}.pkl"
    output_plan = ArtifactOutputPlan(
        name=name,
        path=path,
        artifact_type=MeasurementsArtifactType,
    )
    store = RuntimeValueStore()
    records = {}
    for value, object_name in enumerate(("Nuclei", "Cells", "Cytoplasm"), start=1):
        runtime_value = RuntimeValue.normalize(
            output_plan,
            MeasurementTable(
                name=name,
                rows=MeasurementSparseColumnarRows.from_rows(
                    ({"object_label": 1, "mean_intensity": float(value)},),
                    fields=(
                        FieldSpec("object_label", int),
                        FieldSpec("mean_intensity", float),
                    ),
                ),
                subject=MeasurementSubject(MeasurementScope.OBJECT, object_name),
            ),
            axis_id="A01",
        )
        records[object_name] = store.replace(
            runtime_value,
            path=path,
            backend="memory",
        )
    return (
        store,
        ArtifactInputPlan(
            name=name,
            path=path,
            artifact_type=MeasurementsArtifactType,
        ),
        records,
    )


def _ungrouped_runtime_artifact_input(
    storage_plan: ArtifactInputPlan,
    *,
    axis_scope: RuntimeExecutionAxisScope = RuntimeExecutionAxisScope(axis_id="A01"),
    source_binding_plan: CompiledSourceBindingPlan = CompiledSourceBindingPlan.empty(),
) -> RuntimeArtifactInput:
    ungrouped = ComponentGroupScope.ungrouped()
    return RuntimeArtifactInput(
        edge_plan=_runtime_input_edge(
            storage_plan,
            invocation_scope=ungrouped,
            producer_selection_scope=ungrouped,
            component_scopes=(),
            consumer_variable_components=(),
        ),
        axis_scope=axis_scope,
        backend="memory",
        source_binding_plan=source_binding_plan,
    )


def _paired_channel_label_input(*, producer_axis="A01", producer_values=(), producer_path=None):
    """One exact DNA producer consumed in its paired actin image-set context."""

    fixed_values = {
        AllComponents.CHANNEL: "1",
        AllComponents.SITE: "1",
        AllComponents.Z_INDEX: "1",
        AllComponents.TIMEPOINT: "1",
        **dict(producer_values),
    }
    storage_plan = ArtifactInputPlan(
        name="Nuclei",
        path="/memory/primary/Nuclei.pkl",
        artifact_type=ObjectLabelsArtifactType,
        source_step_id=0,
    )
    output_plan = ArtifactOutputPlan(
        name=storage_plan.name,
        path=producer_path or storage_plan.path,
        artifact_type=storage_plan.artifact_type,
    )
    value = RuntimeValue.normalize_for_execution_scope(
        output_plan,
        ObjectLabelSet(
            name=storage_plan.name,
            variant_data=ObjectLabelVariantData(labels=np.ones((2, 2), dtype=np.uint16)),
        ),
        execution_scope=RuntimeExecutionAxisScope.from_raw(
            producer_axis,
            component=None,
            value=None,
            fixed_component_values=tuple(fixed_values.items()),
        ),
    )
    store = RuntimeValueStore()
    record = store.record(value, path=output_plan.path, backend="memory")
    consumer_scope = RuntimeExecutionAxisScope.from_raw(
        "A01",
        component=None,
        value=None,
        fixed_component_values=(
            (AllComponents.CHANNEL, "2"),
            (AllComponents.SITE, "1"),
            (AllComponents.Z_INDEX, "1"),
            (AllComponents.TIMEPOINT, "1"),
        ),
    )
    source_bindings = CompiledSourceBindingPlan(
        bindings=(NamedSourceBinding(
            alias="Actin",
            component_identity=(ComponentSelector(AllComponents.CHANNEL, "2"),),
        ),),
    )
    runtime_input = _ungrouped_runtime_artifact_input(
        storage_plan,
        axis_scope=consumer_scope,
        source_binding_plan=source_bindings,
    )
    declared_spec = runtime_input.edge_plan.spec.with_group_scope_relation(
        InputGroupLineageSourceRelation(
            source=source_bindings.binding_declarations[0].input_spec().ref()
        )
    )
    return store, record, replace(
        runtime_input,
        edge_plan=replace(runtime_input.edge_plan, spec=declared_spec),
    )


def test_declared_paired_channel_label_input_matches_image_set_context():
    store, record, runtime_input = _paired_channel_label_input()

    assert runtime_input.records(store) == (record,)
    assert runtime_input.resolve_value(store).name == "Nuclei"


def _grouped_label_input_with_distinct_consumer_channel():
    path = "/memory/Cells_channel_0.pkl"
    storage_plan = ArtifactInputPlan(
        name="Cells",
        path=path,
        artifact_type=ObjectLabelsArtifactType,
        group_component=AllComponents.CHANNEL,
        group_keys=("0",),
        paths_by_group={"0": path},
        source_step_id=20,
    )
    output_plan = ArtifactOutputPlan(
        name=storage_plan.name,
        path=path,
        artifact_type=storage_plan.artifact_type,
        group_component=storage_plan.group_component,
        group_keys=storage_plan.group_keys,
        paths_by_group=storage_plan.paths_by_group,
    ).for_group("0")
    value = RuntimeValue.normalize_for_execution_scope(
        output_plan,
        ObjectLabelSet(
            name="Cells",
            variant_data=ObjectLabelVariantData(labels=np.ones((2, 2), dtype=np.uint16)),
        ),
        execution_scope=RuntimeExecutionAxisScope.from_raw(
            "W001", component=AllComponents.CHANNEL, value="0",
            fixed_component_values=(
                (AllComponents.SITE, "1"), (AllComponents.TIMEPOINT, "1"),
            ),
        ),
    )
    store = RuntimeValueStore()
    record = store.record(value, path=path, backend="memory")
    runtime_input = RuntimeArtifactInput(
        edge_plan=_runtime_input_edge(
            storage_plan,
            invocation_scope=ComponentGroupScope.ungrouped(),
            producer_selection_scope=storage_plan.producer_group_scope(),
            component_scopes=(),
            consumer_variable_components=(AllComponents.Z_INDEX,),
        ),
        axis_scope=RuntimeExecutionAxisScope.from_raw(
            "W001", component=None, value=None,
            fixed_component_values=(
                (AllComponents.SITE, "1"), (AllComponents.CHANNEL, "2"),
                (AllComponents.TIMEPOINT, "1"),
            ),
        ),
        backend="memory",
    )
    return store, record, runtime_input


def test_exact_producer_group_does_not_constrain_consumer_source_channel():
    store, record, runtime_input = _grouped_label_input_with_distinct_consumer_channel()

    assert runtime_input.records(store) == (record,)
    assert runtime_input.resolve_value(store) is record.data
    candidates = runtime_input.candidate_execution_scopes(
        store, ComponentGroupScope.ungrouped(),
        variable_components=ComponentSet((AllComponents.Z_INDEX,)),
    )
    (scope,) = candidates
    # Discovery still owns the producer's semantic channel, rather than adopting
    # a later consumer's independently selected source-image channel.
    assert dict(scope.fixed_component_values) == {
        AllComponents.SITE: "1", AllComponents.CHANNEL: "0",
        AllComponents.TIMEPOINT: "1",
    }


@pytest.mark.parametrize("component", [AllComponents.SITE, AllComponents.TIMEPOINT])
def test_exact_producer_group_preserves_shared_fixed_context_constraints(component):
    store, _record, runtime_input = _grouped_label_input_with_distinct_consumer_channel()
    fixed_values = dict(runtime_input.axis_scope.fixed_component_values)
    fixed_values[component] = "2"
    wrong_context = replace(
        runtime_input,
        axis_scope=replace(
            runtime_input.axis_scope, fixed_component_values=tuple(fixed_values.items()),
        ),
    )
    with pytest.raises(RuntimeError, match="Missing RuntimeValueStore record"):
        wrong_context.records(store)


@pytest.mark.parametrize("mismatch", ["group", "well", "path", "fixed-z"])
def test_exact_producer_group_rejects_other_producer_or_fixed_plane(mismatch):
    _store, record, runtime_input = _grouped_label_input_with_distinct_consumer_channel()
    scope = record.key.scope
    path = record.location.path
    if mismatch == "group":
        scope = replace(scope, value="1")
    elif mismatch == "well":
        scope = replace(scope, axis_id="W002")
    elif mismatch == "path":
        path = "/memory/other/Cells_channel_0.pkl"
    else:
        scope = RuntimeExecutionAxisScope.from_raw(
            scope.axis_id, component=scope.component, value=scope.value,
            fixed_component_values=(*scope.fixed_component_values, (AllComponents.Z_INDEX, "2")),
        )
        runtime_input = replace(
            runtime_input,
            axis_scope=RuntimeExecutionAxisScope.from_raw(
                runtime_input.axis_scope.axis_id,
                component=runtime_input.axis_scope.component,
                value=runtime_input.axis_scope.value,
                fixed_component_values=(
                    *runtime_input.axis_scope.fixed_component_values,
                    (AllComponents.Z_INDEX, "1"),
                ),
            ),
        )
    store = RuntimeValueStore()
    store.record(
        replace(record, key=replace(record.key, scope=scope)),
        path=path, backend=record.location.backend,
    )
    with pytest.raises(RuntimeError, match="Missing RuntimeValueStore record"):
        runtime_input.records(store)


def test_different_producer_group_axis_preserves_fixed_source_channel_constraint():
    _store, record, runtime_input = _grouped_label_input_with_distinct_consumer_channel()
    # SITE is now the selected producer group. CHANNEL remains a genuine fixed
    # image context and cannot use the selected-group exemption.
    scope = RuntimeExecutionAxisScope.from_raw(
        "W001", component=AllComponents.SITE, value="1",
        fixed_component_values=(
            (AllComponents.CHANNEL, "0"), (AllComponents.TIMEPOINT, "1"),
        ),
    )
    storage_plan = replace(
        runtime_input.edge_plan.storage_plan,
        group_component=AllComponents.SITE, group_keys=("1",),
        paths_by_group={"1": record.location.path},
    )
    runtime_input = replace(
        runtime_input,
        edge_plan=replace(
            runtime_input.edge_plan,
            storage_plan=storage_plan,
            projection=replace(
                runtime_input.edge_plan.projection,
                producer_selection_scope=storage_plan.producer_group_scope(),
            ),
        ),
    )
    store = RuntimeValueStore()
    store.record(
        replace(record, key=replace(record.key, scope=scope)),
        path=record.location.path, backend=record.location.backend,
    )
    with pytest.raises(RuntimeError, match="Missing RuntimeValueStore record"):
        runtime_input.records(store)


def test_paired_channel_declaration_reaches_both_adapter_input_consumers():
    store, record, runtime_input = _paired_channel_label_input()
    edge = runtime_input.edge_plan

    def consume_labels(image, labels):
        return image

    (source_binding,) = runtime_input.source_binding_plan.binding_declarations
    source_spec = source_binding.input_spec()
    source_edge = InvocationArtifactInputEdgePlan(
        key=InvocationArtifactInputProjectionKey(edge.key.invocation_key, 1),
        spec=source_spec,
        storage_plan=None,
        projection=None,
    )
    contract = CallableContract.from_callable(consume_labels)
    contract = replace(
        contract,
        module_name="SecondaryConsumer",
        metadata=replace(contract.metadata, artifact_inputs=(edge.spec, source_spec)),
    )
    adapter = cellprofiler_runtime_adapter_for_test(
        runtime_value_store=store,
        callable_contract=contract,
        artifact_inputs={edge.key: edge, source_edge.key: source_edge},
        source_binding_plan=runtime_input.source_binding_plan,
        axis_scope=runtime_input.axis_scope,
    )

    projected = adapter.request.runtime_artifact_input(edge, backend=adapter.backend)
    assert projected.edge_plan is edge
    assert projected.axis_scope is adapter.request.axis_scope
    assert projected.source_binding_plan is runtime_input.source_binding_plan
    assert projected.records(store) == (record,)
    assert adapter.artifact_input_records("Nuclei", ObjectLabelsArtifactType) == (record,)
    request = RuntimeInputBindingRequest(
        adapter=adapter, kwargs={}, current_image=np.zeros((2, 2))
    )
    assert request.artifact_value(edge) is record.data


@pytest.mark.parametrize("component", [AllComponents.SITE, AllComponents.Z_INDEX, AllComponents.TIMEPOINT])
def test_paired_channel_input_rejects_other_context_coordinate(component):
    store, _record, runtime_input = _paired_channel_label_input(
        producer_values=((component, "2"),),
    )

    with pytest.raises(RuntimeError, match="Missing RuntimeValueStore record"):
        runtime_input.records(store)


@pytest.mark.parametrize("producer_axis,producer_path", [
    ("B01", None),
    ("A01", "/memory/other_producer/Nuclei.pkl"),
])
def test_paired_channel_input_rejects_other_well_or_producer(producer_axis, producer_path):
    store, _record, runtime_input = _paired_channel_label_input(
        producer_axis=producer_axis, producer_path=producer_path,
    )

    with pytest.raises(RuntimeError, match="Missing RuntimeValueStore record"):
        runtime_input.records(store)


def test_cross_channel_input_without_source_declaration_remains_exact():
    store, _record, runtime_input = _paired_channel_label_input()
    strict_input = replace(
        runtime_input, source_binding_plan=CompiledSourceBindingPlan.empty(),
    )

    with pytest.raises(RuntimeError, match="Missing RuntimeValueStore record"):
        strict_input.records(store)


def test_visible_source_binding_without_context_relation_remains_exact():
    store, _record, runtime_input = _paired_channel_label_input()
    unrelated_input = replace(
        runtime_input,
        edge_plan=replace(
            runtime_input.edge_plan,
            spec=replace(runtime_input.edge_plan.spec, relations=()),
        ),
    )

    with pytest.raises(RuntimeError, match="Missing RuntimeValueStore record"):
        unrelated_input.records(store)


def test_context_relation_to_another_source_does_not_borrow_visible_plane_membership():
    store, _record, runtime_input = _paired_channel_label_input()
    unrelated_input = replace(
        runtime_input,
        edge_plan=replace(
            runtime_input.edge_plan,
            spec=replace(
                runtime_input.edge_plan.spec,
                relations=(InputGroupLineageSourceRelation(
                    ArtifactSpec.input("UnrelatedImage", ImageArtifactType).ref()
                ),),
            ),
        ),
    )

    with pytest.raises(RuntimeError, match="Missing RuntimeValueStore record"):
        unrelated_input.records(store)


def test_paired_channel_projection_rejects_a_different_producer_site_plane():
    store, record, runtime_input = _paired_channel_label_input()
    edge = runtime_input.edge_plan
    payload = replace(
        record.data,
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/source/site2_DNA.tif",),
            component_metadata=({"site": "2", "channel": "1"},),
        ),
    )
    store.replace(
        replace(record, data=payload), path=record.location.path, backend=record.location.backend
    )
    projected_input = replace(
        runtime_input,
        edge_plan=replace(
            edge,
            storage_plan=replace(edge.storage_plan, variable_components=(AllComponents.SITE,)),
            projection=replace(
                edge.projection,
                component_scopes=(ComponentGroupScope(("1",), component=AllComponents.SITE),),
            ),
        ),
    )

    with pytest.raises(RuntimeError, match="no producer plane"):
        projected_input.resolve_value(store)


def test_paired_channel_input_rejects_ambiguous_address_matched_contexts():
    store, _record, runtime_input = _paired_channel_label_input()
    _other_store, other_record, _other_input = _paired_channel_label_input(
        producer_values=((AllComponents.CHANNEL, "3"),),
    )
    store.record(other_record, path=other_record.location.path, backend=other_record.location.backend)

    with pytest.raises(RuntimeError, match="Ambiguous RuntimeValueStore records"):
        runtime_input.records(store)


def test_runtime_artifact_input_preserves_same_scope_semantic_partitions():
    store, storage_plan, records = _same_location_measurement_subject_records()

    assert _ungrouped_runtime_artifact_input(storage_plan).records(store) == tuple(
        records.values()
    )


@pytest.mark.parametrize("producer_values,consumer_values", [
    pytest.param((), (), id="exact-unscoped"),
    pytest.param((), ((AllComponents.Z_INDEX, "1"),), id="consumer-only"),
    pytest.param(((AllComponents.TIMEPOINT, "1"),), (), id="producer-only"),
    pytest.param(
        ((AllComponents.TIMEPOINT, "1"),),
        ((AllComponents.Z_INDEX, "1"),),
        id="disjoint-partial",
    ),
    pytest.param(
        ((AllComponents.TIMEPOINT, "1"),),
        ((AllComponents.Z_INDEX, "1"), (AllComponents.TIMEPOINT, "1")),
        id="shared-partial",
    ),
])
def test_runtime_artifact_input_accepts_exact_unscoped_and_partial_coordinates(
    producer_values, consumer_values,
):
    store = RuntimeValueStore()
    storage_plan = ArtifactInputPlan(
        name="positions",
        path="/memory/positions.pkl",
        artifact_type=MeasurementsArtifactType,
    )
    output_plan = ArtifactOutputPlan(
        name=storage_plan.name,
        path=storage_plan.path,
        artifact_type=storage_plan.artifact_type,
    )
    value = RuntimeValue.normalize_for_execution_scope(
        output_plan,
        MeasurementTable(
            name=storage_plan.name,
            rows=MeasurementSparseColumnarRows.from_rows(
                ({"position": 1.0},),
                fields=(FieldSpec("position", float),),
            ),
            subject=MeasurementSubject(MeasurementScope.ARTIFACT),
        ),
        execution_scope=RuntimeExecutionAxisScope.from_raw(
            "A01",
            component=None,
            value=None,
            fixed_component_values=producer_values,
        ),
    )
    record = store.replace(value, path=storage_plan.path, backend="memory")
    consumer_scope = RuntimeExecutionAxisScope.from_raw(
        "A01",
        component=None,
        value=None,
        fixed_component_values=consumer_values,
    )

    assert _ungrouped_runtime_artifact_input(
        storage_plan,
        axis_scope=consumer_scope,
    ).records(store) == (record,)


@pytest.mark.parametrize("producer_values,consumer_values", [
    pytest.param((), (), id="empty-projected-context"),
    pytest.param(((AllComponents.TIMEPOINT, "1"),), (), id="producer-only"),
    pytest.param((), ((AllComponents.Z_INDEX, "1"),), id="consumer-only"),
    pytest.param(
        ((AllComponents.TIMEPOINT, "1"),),
        ((AllComponents.Z_INDEX, "1"),),
        id="disjoint-partial",
    ),
])
def test_exact_input_admits_no_shared_projected_context_constraints(
    producer_values, consumer_values,
):
    _store, original, original_input = _paired_channel_label_input()
    storage_plan = original_input.edge_plan.storage_plan
    producer_scope = RuntimeExecutionAxisScope.from_raw(
        "A01", component=None, value=None, fixed_component_values=producer_values,
    )
    store = RuntimeValueStore()
    record = store.record(
        RuntimeValue(
            key=replace(original.key, scope=producer_scope),
            data=original.data,
            materialization_source_metadata=original.materialization_source_metadata,
        ),
        path=original.location.path, backend=original.location.backend,
    )
    source = NamedSourceBinding(
        alias="Reference",
        component_identity=(ComponentSelector(get_multiprocessing_axis(), "A01"),),
    )
    consumer_scope = RuntimeExecutionAxisScope.from_raw(
        "A01", component=None, value=None, fixed_component_values=consumer_values,
    )
    runtime_input = _ungrouped_runtime_artifact_input(
        storage_plan, axis_scope=consumer_scope,
        source_binding_plan=CompiledSourceBindingPlan(bindings=(source,)),
    )
    runtime_input = replace(
        runtime_input,
        edge_plan=replace(
            runtime_input.edge_plan,
            spec=runtime_input.edge_plan.spec.with_group_scope_relation(
                InputGroupLineageSourceRelation(source.input_spec().ref())
            ),
        ),
    )

    # Plane-identity compatibility still requires evidence of a shared identity.
    # Exact artifact admission instead has a proven producer/address and only
    # checks the additional coordinates constrained on both sides.
    assert runtime_input.edge_plan.spec.source_context_sources() == (source.input_spec().ref(),)
    policy = SourceImageSetIdentityPolicy.from_source_bindings(runtime_input.source_binding_plan)
    components = ComponentSet.collect(
        (component for component, _value in producer_scope.source_component_values),
        (component for component, _value in consumer_scope.source_component_values),
    )
    assert not SourceImageSetIdentityCompatibility(
        producer_scope.source_image_set_identity(policy, components=components),
        consumer_scope.source_image_set_identity(policy, components=components),
    ).matches()
    assert runtime_input.records(store) == (record,)
    wrong_well = replace(
        runtime_input, axis_scope=replace(consumer_scope, axis_id="B01"),
    )
    wrong_producer = replace(
        runtime_input,
        edge_plan=replace(
            runtime_input.edge_plan,
            storage_plan=replace(storage_plan, path="/memory/other/Nuclei.pkl"),
        ),
    )
    for rejected_input in (wrong_well, wrong_producer):
        with pytest.raises(RuntimeError, match="Missing RuntimeValueStore record"):
            rejected_input.records(store)


def test_runtime_artifact_input_rejects_conflicting_declared_fixed_coordinate():
    store = RuntimeValueStore()
    storage_plan = ArtifactInputPlan(
        name="positions",
        path="/memory/positions.pkl",
        artifact_type=MeasurementsArtifactType,
    )
    output_plan = ArtifactOutputPlan(
        name=storage_plan.name,
        path=storage_plan.path,
        artifact_type=storage_plan.artifact_type,
    )
    value = RuntimeValue.normalize_for_execution_scope(
        output_plan,
        MeasurementTable(
            name=storage_plan.name,
            rows=MeasurementSparseColumnarRows.from_rows(
                ({"position": 1.0},),
                fields=(FieldSpec("position", float),),
            ),
            subject=MeasurementSubject(MeasurementScope.ARTIFACT),
        ),
        execution_scope=RuntimeExecutionAxisScope.from_raw(
            "A01",
            component=None,
            value=None,
            fixed_component_values=((AllComponents.TIMEPOINT, "2"),),
        ),
    )
    store.replace(value, path=storage_plan.path, backend="memory")
    consumer_scope = RuntimeExecutionAxisScope.from_raw(
        "A01",
        component=None,
        value=None,
        fixed_component_values=(
            (AllComponents.Z_INDEX, "1"),
            (AllComponents.TIMEPOINT, "1"),
        ),
    )

    with pytest.raises(RuntimeError, match="Missing RuntimeValueStore record"):
        _ungrouped_runtime_artifact_input(
            storage_plan,
            axis_scope=consumer_scope,
        ).records(store)


def test_runtime_artifact_input_rejects_unprojected_fixed_scope_partitions():
    store = RuntimeValueStore()
    storage_plan = ArtifactInputPlan(
        name="measurements",
        path="/memory/measurements.pkl",
        artifact_type=MeasurementsArtifactType,
    )
    output_plan = ArtifactOutputPlan(
        name=storage_plan.name,
        path=storage_plan.path,
        artifact_type=storage_plan.artifact_type,
    )
    for z_index in ("1", "2"):
        value = RuntimeValue.normalize_for_execution_scope(
            output_plan,
            MeasurementTable(
                name=storage_plan.name,
                rows=MeasurementSparseColumnarRows.from_rows(
                    ({"value": float(z_index)},),
                    fields=(FieldSpec("value", float),),
                ),
                subject=MeasurementSubject(MeasurementScope.ARTIFACT),
            ),
            execution_scope=RuntimeExecutionAxisScope.from_raw(
                "A01",
                component=None,
                value=None,
                fixed_component_values=((AllComponents.Z_INDEX, z_index),),
            ),
        )
        store.replace(value, path=storage_plan.path, backend="memory")

    with pytest.raises(RuntimeError, match="Ambiguous RuntimeValueStore records"):
        _ungrouped_runtime_artifact_input(storage_plan).records(store)


def test_runtime_value_store_merges_observed_records_from_worker_boundary():
    worker_store = RuntimeValueStore()
    value = _runtime_value()
    record = worker_store.record(
        value,
        path="/memory/measurements.pkl",
        backend="memory",
    )

    parent_store = RuntimeValueStore()
    parent_store.merge_observed_values(worker_store.observed_values)
    parent_store.merge_observed_values(worker_store.observed_values)

    assert parent_store.get(value.key) == record
    assert parent_store.observed_values == (record,)


def test_runtime_measurement_observation_axis_accepts_table_record_once():
    value = _runtime_value()
    record = StoredRuntimeValue(
                 key=value.key,
                 data=value.data,
                 materialization_source_metadata=value.materialization_source_metadata,
                 location=RuntimeArtifactLocation(
            path="/memory/measurements.pkl",
            backend="memory",
        ),
             )
    axis = RuntimeMeasurementObservationAxis("A01")

    axis.accept_measurement_table(record)

    assert len(axis.measurement_tables) == 1
    scoped_table = axis.measurement_tables[0]
    assert scoped_table.table is value.data
    assert scoped_table.record_identity == record.location.path
    assert scoped_table.execution_scope == record.key.scope


def test_runtime_value_store_clear_releases_records_and_advances_revision():
    store = RuntimeValueStore()
    value = _runtime_value()
    store.record(value, path="/memory/measurements.pkl", backend="memory")
    revision = store.revision

    store.clear()

    assert store.revision > revision
    assert store.values() == ()
    assert store.observed_values == ()


def test_dynamic_input_query_distinguishes_compiled_paths_with_same_backend():
    store = RuntimeValueStore()
    value = _runtime_value()
    original = store.record(value, path="/first/measurements.pkl", backend="memory")
    later = store.replace(value, path="/second/measurements.pkl", backend="memory")
    queries = tuple(
        RuntimeArtifactQuery.from_input_plan(
            ArtifactInputPlan(
                name="measurements",
                path=record.location.path,
                artifact_type=MeasurementsArtifactType,
                group_component=AllComponents.CHANNEL,
                paths_by_group={None: record.location.path, "DAPI": record.location.path},
            ),
            axis_id="A01",
            backend="memory",
        )
        for record in (original, later)
    )
    assert queries[0] != queries[1]
    assert store.find_matching(queries[0]) == (original,)
    assert store.find_matching(queries[1]) == (later,)
    assert store.find_matching(queries[0]) == (original,)


def test_dynamic_input_query_retains_discovery_order_and_ignores_wrong_component():
    store = RuntimeValueStore()
    value = _runtime_value()
    wrong = RuntimeValue.normalize(
        ArtifactOutputPlan(
            name="measurements",
            path="/memory/measurements.pkl",
            artifact_type=MeasurementsArtifactType,
            group_component=AllComponents.SITE,
            group_keys=("DAPI",),
        ),
        value.data,
        axis_id="A01",
    )
    store.record(wrong, path="/memory/measurements.pkl", backend="memory")
    original = store.record(value, path="/memory/measurements.pkl", backend="memory")
    query = RuntimeArtifactQuery.from_input_plan(
        ArtifactInputPlan(
            name="measurements",
            path="/memory/measurements.pkl",
            artifact_type=MeasurementsArtifactType,
            group_component=AllComponents.CHANNEL,
        ),
        axis_id="A01",
        backend="memory",
    )
    assert store.find_matching(query) == (original,)


def test_dynamic_query_snapshots_address_mapping_without_mutating_source_plan():
    paths = {None: "/memory/measurements.pkl", "DAPI": "/first/measurements.pkl"}
    plan = ArtifactInputPlan(
        name="measurements",
        path="/memory/measurements.pkl",
        artifact_type=MeasurementsArtifactType,
        group_component=AllComponents.CHANNEL,
        paths_by_group=paths,
    )
    old_query = RuntimeArtifactQuery.from_input_plan(
        plan, axis_id="A01", backend="memory"
    )
    same_query = RuntimeArtifactQuery.from_input_plan(
        plan, axis_id="A01", backend="memory"
    )
    old_hash = hash(old_query)
    assert old_query == same_query
    store = RuntimeValueStore()
    value = _runtime_value()
    first = store.record(value, path=paths["DAPI"], backend="memory")
    assert store.find_matching(old_query) == (first,)
    paths["DAPI"] = "/second/measurements.pkl"
    assert plan.paths_by_group is paths
    assert old_query.target.input_plan.paths_by_group["DAPI"] == first.location.path
    assert hash(old_query) == old_hash
    assert old_query == same_query
    assert store.find_matching(old_query) == (first,)
    new_query = RuntimeArtifactQuery.from_input_plan(
        plan, axis_id="A01", backend="memory"
    )
    assert new_query != old_query
    assert store.find_matching(new_query) == ()
    second = store.replace(value, path=paths["DAPI"], backend="memory")
    assert store.find_matching(old_query) == (first,)
    assert store.find_matching(new_query) == (second,)
    with pytest.raises(TypeError):
        old_query.target.input_plan.paths_by_group["DAPI"] = "/mutated/query.pkl"


@pytest.mark.parametrize("paths", (None, {}))
def test_dynamic_query_retains_absent_and_empty_path_declarations(paths):
    plan = ArtifactInputPlan(
        name="measurements",
        path="/memory/measurements.pkl",
        artifact_type=MeasurementsArtifactType,
        group_component=AllComponents.CHANNEL,
        paths_by_group=paths,
    )
    query = RuntimeArtifactQuery.from_input_plan(plan, axis_id="A01", backend="memory")
    assert query.target.input_plan.paths_by_group == paths
    assert plan.paths_by_group is paths
    assert query.target.input_plan.path_for_runtime_query("DAPI") == plan.path


def test_input_plan_owns_independent_immutable_runtime_address_snapshot():
    paths = {None: "/memory/measurements.pkl", "DAPI": "/first/measurements.pkl"}
    plan = ArtifactInputPlan(
        name="measurements",
        path="/memory/measurements.pkl",
        artifact_type=MeasurementsArtifactType,
        group_component=AllComponents.CHANNEL,
        paths_by_group=paths,
        source_step_id=7,
        source_step_scope_id="producer-scope",
    )
    snapshot = plan.runtime_query_snapshot()
    assert snapshot == plan
    assert snapshot is not plan
    assert snapshot.paths_by_group is not paths
    assert plan.paths_by_group is paths
    paths["DAPI"] = "/second/measurements.pkl"
    assert snapshot.path_for_runtime_query("DAPI") == "/first/measurements.pkl"
    assert plan.path_for_runtime_query("DAPI") == "/second/measurements.pkl"
    assert snapshot.source_step_id == plan.source_step_id
    assert snapshot.source_step_scope_id == plan.source_step_scope_id
    with pytest.raises(TypeError):
        snapshot.paths_by_group["DAPI"] = "/mutated/query.pkl"


def test_store_transport_excludes_all_derived_lookup_caches():
    store = RuntimeValueStore()
    value = _runtime_value()
    value.data.rows = MeasurementProjectedColumnarRows(
        {"object_id": (1,)}, fields=(FieldSpec("object_id", int),)
    )
    record = store.record(value, path="/memory/measurements.pkl", backend="memory")
    latest = store.replace(
        value, path="/later/measurements.pkl", backend="memory"
    )
    original_transport = pickle.dumps(store, protocol=5)
    query = RuntimeArtifactQuery.from_input_plan(
        ArtifactInputPlan(
            name="measurements",
            path=record.location.path,
            artifact_type=MeasurementsArtifactType,
            group_component=AllComponents.CHANNEL,
            paths_by_group={"DAPI": record.location.path},
        ),
        axis_id="A01",
        backend="memory",
    )
    assert store.find(name=value.key.name) == (record, latest)
    assert store.find_matching(query) == (record,)
    store.query_cache(RuntimeObjectLabelMeasurementQueryCache).store_value(
        _label_query(), (np.ones(100_000),)
    )
    assert pickle.dumps(store, protocol=5) == original_transport
    restored = pickle.loads(original_transport)
    assert restored.revision == store.revision
    assert "_find_cache" not in vars(store)
    assert "_find_matching_cache" not in vars(store)
    assert "_find_cache" not in vars(restored)
    assert "_find_matching_cache" not in vars(restored)
    assert restored._query_caches == {}
    assert restored.values()[0].key == record.key
    assert restored.values()[0].location == record.location
    assert restored.values()[0].data.row_mappings() == value.data.row_mappings()
    assert restored.find_matching(query) == (restored.values()[0],)
    assert restored.get(record.key) is restored.values()[1]
    assert restored.get(record.key).location == latest.location
    assert restored.observed_values == restored.values()
    assert restored.values()[0] is restored.observed_values[0]
    assert restored.values()[0].data is restored.values()[1].data
    assert restored.values()[0].key is restored.values()[1].key


def test_unified_store_cache_keeps_both_query_domains_and_empty_results():
    from openhcs.core.process_local_cache import BoundedCache

    store = RuntimeValueStore()
    record = store.record(_runtime_value(), path="/memory/measurements.pkl", backend="memory")
    query = RuntimeArtifactQuery.from_input_plan(
        ArtifactInputPlan(
            name="measurements",
            path=record.location.path,
            artifact_type=MeasurementsArtifactType,
            group_component=AllComponents.CHANNEL,
        ),
        axis_id="A01",
        backend="memory",
    )
    semantic = store.find(name=record.key.name)
    planned = store.find_matching(query)
    empty = store.find(name="absent")
    assert semantic == planned == (record,)
    assert store.find(name=record.key.name) is semantic
    assert store.find_matching(query) is planned
    cache = store.query_cache(BoundedCache)
    assert len(cache.entries) == 3
    assert empty == ()
    assert sum(value == () for value in cache.entries.values()) == 1
    assert store.find(name="absent") is empty
    assert len(cache.entries) == 3


def test_unified_store_cache_eviction_recomputes_order_without_changing_record_aliases():
    from openhcs.core.process_local_cache import BoundedCache

    store = RuntimeValueStore()
    first_value = _runtime_value(name="first")
    second_value = _runtime_value(name="second")
    first = store.record(first_value, path="/memory/first.pkl", backend="memory")
    second = store.record(second_value, path="/memory/second.pkl", backend="memory")
    cache = store.query_cache(BoundedCache)
    cache.max_entries = 2
    all_records = store.find()
    assert all_records == (first, second)
    query = RuntimeArtifactQuery.from_output_plan(
        ArtifactOutputPlan(
            name="first",
            path=first.location.path,
            artifact_type=MeasurementsArtifactType,
            group_component=AllComponents.CHANNEL,
            group_keys=("DAPI",),
        ),
        axis_id="A01",
        backend="memory",
        group_key="DAPI",
    )
    assert store.find_matching(query) == (first,)
    assert store.find(name="missing") == ()
    assert len(cache.entries) == 2
    recomputed = store.find()
    assert recomputed == all_records
    assert recomputed is not all_records
    assert recomputed[0] is first and recomputed[1] is second
    replacement = store.replace(first_value, path=first.location.path, backend="memory")
    assert cache.entries == {}
    assert store.find_matching(query)[0] is replacement
    assert store.find() == (replacement, second)
    assert store.find()[1] is second


def test_changed_stored_measurement_subject_requires_a_transient_value():
    value = _runtime_value()
    store = RuntimeValueStore()
    record = store.record(value, path="/memory/measurements.pkl", backend="memory")
    plan = ArtifactOutputPlan(
        name=value.name, artifact_type=value.artifact_type,
        path="/memory/measurements.pkl",
    )
    record.data.subject = MeasurementSubject(MeasurementScope.IMAGE, "NextImage")

    admitted = record.validated_for_output_plan(plan, axis_id="A01")

    assert type(admitted) is RuntimeValue
    assert admitted.key.semantic_id == record.data.runtime_semantic_id
    assert admitted.key != record.key
    assert store.get(record.key) is record
    assert record.location.path == "/memory/measurements.pkl"
    assert admitted.data is record.data
    assert type(StoredRuntimeValue.from_output_plan(
        plan, admitted.data, execution_scope=record.key.scope,
    )) is RuntimeValue
