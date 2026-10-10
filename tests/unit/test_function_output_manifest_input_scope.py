from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from openhcs.core.aligned_image_payload import AlignedImageSliceContext
from openhcs.core.artifacts import (
    ArtifactInputPlan,
    ArtifactOutputPlan,
    ArtifactInputProjectionPlan,
    ArtifactSpec,
    ImageArtifactType,
    MeasurementsArtifactType,
    ObjectLabelsArtifactType,
)
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_metadata import (
    SOURCE_VOXEL_SPACING_FIELD,
    SourceVoxelSpacing,
)
from openhcs.core.function_patterns import (
    MainFlowInputProjection,
    InvocationArtifactInputEdgePlan,
    InvocationArtifactInputProjectionKey,
    compile_function_pattern,
)
from openhcs.core.pipeline.function_contracts import artifact_inputs, artifact_outputs
from openhcs.core.step_dependencies import StepInputDependency
from openhcs.core.steps.function_output_identity import FunctionOutputIdentity
from openhcs.core.steps.function_output_manifest import (
    ProducedOutputSemantics,
    StepOutputManifestStore,
)
from openhcs.core.dataset_sources.source_schema import SourceSchemaFilenameParser
from openhcs.domains.microscopy.axes import Microscopy


def test_artifact_output_kind_is_owned_by_original_compiled_plan() -> None:
    plan = CompiledStepPlan(
        step_index=3,
        step_name="IdentifyCells",
        step_scope_id="identify-cells",
        pipeline_position=3,
        axis_id="A01",
    )
    output = ArtifactOutputPlan(
        name="cells", path="cells.pkl", artifact_type=ObjectLabelsArtifactType,
    )
    identity = plan.producer_identity_for_artifact(output)

    assert identity.output_kind == CompiledStepPlan.ARTIFACT_OUTPUT_KIND
    assert identity.output_key == identity.projection_key == "cells"
    assert identity.artifact_kind == ObjectLabelsArtifactType.value
    assert identity.step_name == "IdentifyCells"
    assert identity.step_scope_id == "identify-cells"
    assert identity.pipeline_position == 3


def test_producer_identity_reads_current_plan_and_original_surface() -> None:
    plan = CompiledStepPlan(
        step_index=1, step_name="Original",
        step_scope_id="original", pipeline_position=1, axis_id="A01",
    )
    surface = AlignedImageSliceContext.main_flow("corrected")
    original = plan.producer_identity_for_main_flow(surface)
    plan.step_name = "Replacement"
    plan.step_scope_id = "replacement"
    plan.pipeline_position = 2
    replacement = plan.producer_identity_for_main_flow(surface)

    assert original.step_name == "Original"
    assert original.step_scope_id == "original"
    assert original.pipeline_position == 1
    assert replacement.step_name == "Replacement"
    assert replacement.step_scope_id == "replacement"
    assert replacement.pipeline_position == 2
    assert replacement.output_kind == surface.output_kind
    assert replacement.output_key == surface.output_key
    assert replacement.projection_key == surface.projection_key
    assert replacement.artifact_kind == surface.artifact_kind


@pytest.mark.parametrize("saved_path", ("/saved/image.tif", "image.tif"))
def test_produced_occurrence_owns_memory_path_and_current_source_projection(
    saved_path: str,
) -> None:
    plan = CompiledStepPlan(
        step_index=1, step_name="Producer", axis_id="A01",
        step_scope_id="producer", pipeline_position=1, output_dir=Path("/memory"),
    )
    components = {"well": "A01", "channel": 2}
    record = ProducedOutputSemantics(
        producer_identity=plan.producer_identity_for_main_flow(
            AlignedImageSliceContext.anonymous_main_flow()
        ),
        component_values=components,
        filename_component_values={"well": "A01", "channel": 9},
        extension=".tif", source="test", output_path=saved_path,
        relative_output_path="nested/image.tif",
    )
    assert record.memory_path(plan) == (
        saved_path if saved_path.startswith("/") else "/memory/nested/image.tif"
    )
    metadata = ImagePayloadMetadata(
        source_component_metadata={"acquisition": "first", "channel": 1},
        source_voxel_spacing=SourceVoxelSpacing((0.5, 0.5)),
    )
    original = record.source_metadata_for_projection(metadata, "/disk/output.tif")
    assert original["channel"] == "2"
    assert original["acquisition"] == "first"
    assert original[SOURCE_VOXEL_SPACING_FIELD] == "0.5,0.5"
    components["channel"] = 3
    metadata.source_component_metadata = {"acquisition": "second", "channel": 1}
    current = record.source_metadata_for_projection(metadata, "/disk/output.tif")
    assert current["channel"] == "3"
    assert current["acquisition"] == "second"
    assert original["channel"] == "2"
    assert record.filename_values["channel"] == 9

    metadata.source_component_metadata = {SOURCE_VOXEL_SPACING_FIELD: "1,1"}
    with pytest.raises(RuntimeError, match="Conflicting source voxel spacing.*output.tif"):
        record.source_metadata_for_projection(metadata, "/disk/output.tif")


def test_published_slots_stay_fixed_with_live_source_metadata_and_filename_aliases():
    plan = CompiledStepPlan(
        step_index=1, step_name="Producer", axis_id="A01",
        step_scope_id="producer", pipeline_position=1, output_dir=Path("/memory"),
    )
    coordinates = [{"channel": 1}, {"channel": 2}]
    metadata = ImagePayloadMetadata(source_component_metadata={"acquisition": "first"})
    records = tuple(
        ProducedOutputSemantics.from_output(
            plan, plan.output_dir / f"channel{channel}.tif",
            FunctionOutputIdentity(values, ".tif", "test"),
            image_metadata=metadata,
        )
        for channel, values in enumerate(coordinates, 1)
    )
    manifest = StepOutputManifestStore()
    manifest.begin_step(plan)
    manifest.record_outputs(plan, records)
    coordinates[0]["channel"] = 2
    metadata.source_component_metadata = {"acquisition": "second"}
    manifest.record_outputs(plan, ())
    published = manifest.produced_records_for(plan)
    assert tuple(record.component_values["channel"] for record in published) == (1, 2)
    assert published[0].filename_values["channel"] == 2
    assert records[0].component_values["channel"] == 2
    projection = published[0].source_metadata_for_projection(metadata, "/saved/image.tif")
    assert projection["channel"] == "1"
    assert projection["acquisition"] == "second"
    replacement = replace(records[0], component_values={"channel": 1}, output_path="new.tif")
    manifest.record_outputs(plan, (replacement,))
    assert tuple(record.output_path for record in manifest.produced_records_for(plan)) == (
        "new.tif", "/memory/channel2.tif",
    )


def _compiled_pattern_with_input_edges(
    specs_with_scopes: tuple[tuple[ArtifactSpec, str], ...],
):
    specs = tuple(spec for spec, _scope in specs_with_scopes)

    @artifact_inputs(*specs)
    def consume(image, *, labels=None, illumination_function=None):
        return image

    compiled = compile_function_pattern(consume, {}, {})
    invocation = compiled.default_group.invocations[0]
    edges = []
    for input_index, (spec, source_scope_id) in enumerate(specs_with_scopes):
        storage_plan = ArtifactInputPlan(
            name=spec.name,
            path=spec.name,
            artifact_type=spec.artifact_type,
            source_step_scope_id=source_scope_id,
        )
        producer_scope = storage_plan.producer_group_scope()
        edges.append(
            InvocationArtifactInputEdgePlan(
                key=InvocationArtifactInputProjectionKey(
                    invocation_key=invocation.key,
                    input_index=input_index,
                ),
                spec=spec,
                storage_plan=storage_plan,
                projection=ArtifactInputProjectionPlan(
                    invocation_scope=producer_scope,
                    producer_selection_scope=producer_scope,
                ),
            )
        )
    invocation = invocation.with_artifact_input_edges(tuple(edges))
    group = replace(compiled.default_group, invocations=(invocation,))
    return replace(compiled, groups=(group,))


@pytest.mark.parametrize(
    (
        "dependency_scope",
        "producer_output_name",
        "producer_artifact_type",
        "producer_channel",
        "foreign_inputs",
    ),
    (
        pytest.param(
            "display_data",
            "DisplayImage",
            ImageArtifactType,
            2,
            (
                (ArtifactSpec.input("Nuclei", ObjectLabelsArtifactType), "identify"),
                (
                    ArtifactSpec.input("ObjectMeasurements", MeasurementsArtifactType),
                    "measure_intensity",
                ),
            ),
            id="ExamplePercentPositive-ClassifyObjects",
        ),
        pytest.param(
            "identify_tumor",
            "tumor",
            ObjectLabelsArtifactType,
            1,
            (
                (ArtifactSpec.input("GrayTumor", ImageArtifactType), "color_to_gray"),
                (ArtifactSpec.input("GrayLung", ImageArtifactType), "color_to_gray"),
            ),
            id="ExampleTumor-ImageMath",
        ),
    ),
)
def test_foreign_artifact_inputs_do_not_filter_lifecycle_producer(
    tmp_path: Path,
    dependency_scope: str,
    producer_output_name: str,
    producer_artifact_type,
    producer_channel: int,
    foreign_inputs: tuple[tuple[ArtifactSpec, str], ...],
) -> None:
    output_dir = tmp_path / "images"
    producer = CompiledStepPlan(
        step_index=1,
        step_scope_id=dependency_scope,
        step_name="LifecycleProducer",
        pipeline_position=1,
        axis_id="A01",
        output_dir=output_dir,
    )
    consumer = SimpleNamespace(
        axis_id="A01",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=1,
            source_step_scope_id=dependency_scope,
        ),
        compiled_function_pattern=_compiled_pattern_with_input_edges(foreign_inputs),
    )
    producer_path = output_dir / (
        f"A01_s001_w{producer_channel}_z001_t001_{producer_output_name}.tif"
    )
    store = StepOutputManifestStore()
    store.begin_step(producer)
    store.record_outputs(
        producer,
        (
            ProducedOutputSemantics.from_output(
                producer,
                producer_path,
                FunctionOutputIdentity(
                    component_values={
                        "well": "A01",
                        "site": 1,
                        "channel": producer_channel,
                        "z_index": 1,
                        "timepoint": 1,
                    },
                    extension=".tif",
                    source="test",
                ),
                output_context=AlignedImageSliceContext.main_flow(
                    output_key=producer_output_name,
                    artifact_kind=producer_artifact_type.value,
                ),
            ),
        ),
    )

    assert store.filter_to_producer_paths(
        consumer,
        [
            "A01_s001_w9_z001_t001_unrelated.tif",
            producer_path.name,
        ],
        SourceSchemaFilenameParser(),
    ) == [producer_path.name]


def test_compiled_main_flow_edge_selects_exact_producer_identity(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "images"
    producer = CompiledStepPlan(
        step_index=1,
        step_scope_id="align",
        step_name="Align",
        pipeline_position=1,
        axis_id="A01",
        output_dir=output_dir,
    )
    input_spec = ArtifactSpec.input("Stain1", ImageArtifactType)

    @artifact_inputs(input_spec)
    def consume(image):
        return image

    compiled = compile_function_pattern(consume, {}, {})
    invocation = compiled.default_group.invocations[0]
    invocation = invocation.with_artifact_input_edges(
        (
            InvocationArtifactInputEdgePlan(
                key=InvocationArtifactInputProjectionKey(
                    invocation_key=invocation.key,
                    input_index=0,
                ),
                spec=input_spec,
                storage_plan=None,
                projection=None,
                main_flow_projection=MainFlowInputProjection.DECLARED_SOURCE_IMAGE,
            ),
        )
    )
    compiled = replace(
        compiled,
        groups=(replace(compiled.default_group, invocations=(invocation,)),),
    )
    consumer = SimpleNamespace(
        axis_id="A01",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=1,
            source_step_scope_id="align",
        ),
        compiled_function_pattern=compiled,
    )
    store = StepOutputManifestStore()
    store.begin_step(producer)
    store.record_outputs(
        producer,
        tuple(
            ProducedOutputSemantics.from_output(
                producer,
                output_dir / f"A01_s001_w{channel}_z001_t001.tif",
                FunctionOutputIdentity(
                    component_values={
                        "well": "A01",
                        "site": 1,
                        "channel": channel,
                    },
                    extension=".tif",
                    source="test",
                ),
                output_context=AlignedImageSliceContext.main_flow(
                    output_key=output_key,
                    artifact_kind=ImageArtifactType.value,
                ),
            )
            for channel, output_key in ((1, "Stain1"), (2, "Stain2"))
        ),
    )

    assert store.filter_to_producer_paths(
        consumer,
        [
            "A01_s001_w1_z001_t001.tif",
            "A01_s001_w2_z001_t001.tif",
        ],
        SourceSchemaFilenameParser(),
    ) == ["A01_s001_w1_z001_t001.tif"]


def test_storage_backed_primary_input_selects_exact_lifecycle_output(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "images"
    producer = CompiledStepPlan(
        step_index=1,
        step_scope_id="color_to_gray",
        step_name="ColorToGray",
        pipeline_position=1,
        axis_id="A01",
        output_dir=output_dir,
    )
    source = ArtifactSpec.input("OrigRed", ImageArtifactType)
    illumination = ArtifactSpec.output_inheriting_group_scope(
        "IllumRed",
        ImageArtifactType,
        source,
    )

    @artifact_inputs(source)
    @artifact_outputs(illumination)
    def calculate_illumination(image):
        return image

    compiled = compile_function_pattern(calculate_illumination, {}, {})
    invocation = compiled.default_group.invocations[0]
    storage_plan = ArtifactInputPlan(
        name=source.name,
        path=source.name,
        artifact_type=source.artifact_type,
        source_step_scope_id="color_to_gray",
    )
    producer_scope = storage_plan.producer_group_scope()
    invocation = invocation.with_artifact_input_edges(
        (
            InvocationArtifactInputEdgePlan(
                key=InvocationArtifactInputProjectionKey(
                    invocation_key=invocation.key,
                    input_index=0,
                ),
                spec=source,
                storage_plan=storage_plan,
                projection=ArtifactInputProjectionPlan(
                    invocation_scope=producer_scope,
                    producer_selection_scope=producer_scope,
                ),
            ),
        )
    )
    compiled = replace(
        compiled,
        groups=(replace(compiled.default_group, invocations=(invocation,)),),
    )
    consumer = SimpleNamespace(
        axis_id="A01",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=1,
            source_step_scope_id="color_to_gray",
        ),
        compiled_function_pattern=compiled,
    )
    store = StepOutputManifestStore()
    store.begin_step(producer)
    store.record_outputs(
        producer,
        tuple(
            ProducedOutputSemantics.from_output(
                producer,
                output_dir / f"A01_s001_w1_z001_t001_{output_key}.tif",
                FunctionOutputIdentity(
                    component_values={
                        "well": "A01",
                        "site": 1,
                        "channel": 1,
                    },
                    extension=".tif",
                    source="test",
                ),
                output_context=AlignedImageSliceContext.main_flow(
                    output_key=output_key,
                    artifact_kind=ImageArtifactType.value,
                ),
            )
            for output_key in ("OrigRed", "OrigGreen", "OrigBlue")
        ),
    )

    assert store.filter_to_producer_paths(
        consumer,
        [
            "A01_s001_w1_z001_t001_OrigBlue.tif",
            "A01_s001_w1_z001_t001_OrigGreen.tif",
            "A01_s001_w1_z001_t001_OrigRed.tif",
        ],
        SourceSchemaFilenameParser(),
    ) == ["A01_s001_w1_z001_t001_OrigRed.tif"]


def test_storage_backed_input_does_not_reclassify_lifecycle_output(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "images"
    producer = CompiledStepPlan(
        step_index=1,
        step_scope_id="artifact_producer",
        step_name="ArtifactProducer",
        pipeline_position=1,
        axis_id="A01",
        output_dir=output_dir,
    )
    stored_input = ArtifactSpec.input("StoredLabels", ObjectLabelsArtifactType)
    consumer = SimpleNamespace(
        axis_id="A01",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=1,
            source_step_scope_id="artifact_producer",
        ),
        compiled_function_pattern=_compiled_pattern_with_input_edges(
            ((stored_input, "artifact_producer"),)
        ),
    )
    lifecycle_path = output_dir / "A01_s001_w2_z001_t001.tif"
    store = StepOutputManifestStore()
    store.begin_step(producer)
    store.record_outputs(
        producer,
        (
            ProducedOutputSemantics.from_output(
                producer,
                lifecycle_path,
                FunctionOutputIdentity(
                    component_values={
                        "well": "A01",
                        "site": 1,
                        "channel": 2,
                    },
                    extension=".tif",
                    source="test",
                ),
                output_context=AlignedImageSliceContext.main_flow(
                    output_key="LifecycleImage",
                    artifact_kind=ImageArtifactType.value,
                ),
            ),
        ),
    )

    assert store.filter_to_producer_paths(
        consumer,
        [
            "A01_s001_w1_z001_t001.tif",
            lifecycle_path.name,
        ],
        SourceSchemaFilenameParser(),
    ) == [lifecycle_path.name]


@pytest.mark.parametrize(
    ("artifact_type", "parameter_name"),
    (
        pytest.param(
            ObjectLabelsArtifactType,
            "labels",
            id="object-label-runtime-argument",
        ),
        pytest.param(
            ImageArtifactType,
            "illumination_function",
            id="auxiliary-image-runtime-argument",
        ),
    ),
)
def test_same_scope_parameter_bound_input_does_not_select_lifecycle_output(
    tmp_path: Path,
    artifact_type,
    parameter_name: str,
) -> None:
    output_dir = tmp_path / "images"
    producer = CompiledStepPlan(
        step_index=1,
        step_scope_id="artifact_producer",
        step_name="ArtifactProducer",
        pipeline_position=1,
        axis_id="A01",
        output_dir=output_dir,
    )
    auxiliary_input = ArtifactSpec.input(
        "AuxiliaryArtifact",
        artifact_type,
        parameter_name=parameter_name,
    )
    consumer = SimpleNamespace(
        axis_id="A01",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=1,
            source_step_scope_id="artifact_producer",
        ),
        compiled_function_pattern=_compiled_pattern_with_input_edges(
            ((auxiliary_input, "artifact_producer"),)
        ),
    )
    producer_path = output_dir / "A01_s001_w1_z001_t001.tif"
    store = StepOutputManifestStore()
    store.begin_step(producer)
    store.record_outputs(
        producer,
        (
            ProducedOutputSemantics.from_output(
                producer,
                producer_path,
                FunctionOutputIdentity(
                    component_values={
                        "well": "A01",
                        "site": 1,
                        "channel": 1,
                    },
                    extension=".tif",
                    source="test",
                ),
                output_context=AlignedImageSliceContext.main_flow(
                    output_key="PreservedInput",
                    artifact_kind=ImageArtifactType.value,
                ),
            ),
        ),
    )

    assert store.filter_to_producer_paths(
        consumer,
        [producer_path.name],
        SourceSchemaFilenameParser(),
    ) == [producer_path.name]


def test_named_producer_members_keep_acquisition_filters_and_site_correlations():
    from openhcs.core.source_bindings import (
        CompiledSourceBindingPlan, ComponentSelector, NamedSourceBinding,
        SourceFilterClause, SourceFilterMatchType, SourceFilterSubject, SourceSelector,
    )
    from openhcs.core.source_matching import SourceImageSetIdentityPolicy
    from openhcs.core.source_metadata import SourceFilterPathMetadata
    from openhcs.core.steps.function_output_manifest import ProducedPathRecordIndex
    from openhcs.core.dataset_sources.source_schema import SourceSchemaFilenameParser

    parser = SourceSchemaFilenameParser()
    plan = CompiledStepPlan(
        step_index=2, step_name="Align", axis_id="A01",
        step_scope_id="align", pipeline_position=2, output_dir=Path("/memory"),
    )
    records = []
    for site in (1, 2):
        for channel, marker in ((1, "N_R"), (2, "N_G")):
            components = dict(well="A01", site=site, channel=channel, z_index=1, timepoint=1)
            acquisition_path = f"/acquisition/0_{site}_{marker}.png"
            source_metadata = dict(components)
            SourceFilterPathMetadata.from_paths(
                (Path(acquisition_path).name, acquisition_path)
            ).merge_into(source_metadata, path=acquisition_path)
            identity = FunctionOutputIdentity(
                components, ".tif", "test", filename_qualifier=f"Stain{channel}",
            )
            records.append(ProducedOutputSemantics.from_output(
                plan, plan.output_dir / identity.filename(parser), identity,
                output_context=AlignedImageSliceContext.main_flow(f"Stain{channel}", artifact_kind="image"),
                image_metadata=ImagePayloadMetadata(
                    source_path=acquisition_path, source_component_metadata=source_metadata,
                ),
            ).published())
    bindings = CompiledSourceBindingPlan(bindings=(NamedSourceBinding(
        alias="OrigStain1",
        selector=SourceSelector(filters=(SourceFilterClause(
            SourceFilterSubject.FILE, SourceFilterMatchType.CONTAINS, "N_R",
        ),)),
        component_identity=(ComponentSelector(Microscopy.Channel, "1"),),
    ),))
    index = ProducedPathRecordIndex.from_records(tuple(records), parser)
    anchors = index.matching_records("A01_s{iii}_w1_z001_t001.tif")
    selected = index.source_binding_members(
        tuple(record.output_path for record in anchors), source_bindings=bindings,
        identity_policy=SourceImageSetIdentityPolicy(), parser=parser,
    )
    assert selected == (records[0], records[2])
    assert tuple(record.component_values["site"] for record in selected) == (1, 2)
    wrong_binding = replace(bindings, bindings=(replace(
        bindings.bindings[0], selector=SourceSelector(filters=(SourceFilterClause(
            SourceFilterSubject.FILE, SourceFilterMatchType.CONTAINS, "absent",
        ),)),
    ),))
    assert index.source_binding_members(
        tuple(record.output_path for record in anchors), source_bindings=wrong_binding,
        identity_policy=SourceImageSetIdentityPolicy(), parser=parser,
    ) == ()
