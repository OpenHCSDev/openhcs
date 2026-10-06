from openhcs.core.steps.function_runtime import (
    PatternGroupExecutionRequest,
    PatternGroupExecutionScope,
    PatternGroupData,
    FunctionCoreExecutor,
)
from collections.abc import Callable
from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import Mock

import numpy as np
import pytest
from objectstate.global_config import GlobalContextValues
from polystore.virtual_workspace import SourcePixelRef

from openhcs.constants.constants import (
    AllComponents,
    Backend,
    GroupBy,
    VariableComponents,
)
from openhcs.core.aligned_image_payload import (
    AlignedImageSliceContext,
    ImagePayloadBundleContext,
    payload_slices_for_alignment,
    stack_image_payloads,
)
from openhcs.core.artifacts import (
    ArtifactInputPlan,
    ArtifactMeasurementSubjectRelation,
    ArtifactOutputPlan,
    ArtifactSidecarRole,
    ArtifactSpec,
    GroupLineageSourceRelation,
    ImageArtifactType,
    MeasurementsArtifactType,
    ObjectLabelsArtifactType,
)
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.config import GlobalPipelineConfig
from openhcs.core.component_group_scope import (
    ComponentGroupScope,
)
from openhcs.core.component_set import ComponentSet
from openhcs.core.function_patterns import (
    MainFlowInputProjection,
    InvocationArtifactInputEdgePlan,
    InvocationArtifactInputProjectionKey,
    RuntimeInvocationDomain,
    compile_function_pattern,
)
from openhcs.core.memory.decorators import numpy as numpy_memory
from openhcs.core.pipeline.function_contracts import (
    artifact_inputs,
    artifact_outputs,
    composed_image_payload,
    special_inputs,
)
from openhcs.core.pipeline.path_planner import PathPlanner, PathPlannerArtifactStage
from openhcs.core.pipeline.compiler import PipelineCompiler
from openhcs.core.artifact_key_selection import AdapterRecordedArtifactOutputPolicy
from openhcs.core.runtime_adapters import runtime_adapter
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    ImagePayloadMetadataCompositionMode,
    image_payload_data,
    image_payload_metadata,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.runtime_stack_cache import RuntimeImageStackCache
from openhcs.core.source_binding_selection import SourcePatternResolutionContext
from openhcs.core.runtime_source_binding_cache import RuntimeSourceBindingContextCache
from openhcs.core.runtime_pattern_cache import RuntimePatternDiscoveryCache
from openhcs.core.steps.function_output_manifest import _STEP_OUTPUT_MANIFESTS
from openhcs.core.source_bindings import (
    SOURCE_BINDING_ALIAS_METADATA_FIELD,
    CompiledSourceBindingPlan,
    ComponentSelector,
    NamedSourceBinding,
    SourceBindingMatchMethod,
    SourceBindingMatchPlan,
    SourceBindingOrigin,
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
    SourceProjectionRole,
    SourceSelector,
)
from openhcs.core.source_image_provenance import (
    SourceImageProvenancePlanes,
)
from openhcs.core.source_matching import SourceImageSetIdentityPolicy
from openhcs.core.source_metadata import SourceFilterPathMetadata
from openhcs.core.source_projection import (
    OpenHCSPlaneAddress,
    SourceArtifactProjection,
    SourcePlaneProjection,
    SourceProjectionSet,
)
from openhcs.core.source_workspace_projection import (
    VirtualWorkspaceSourceProjectionAuthority,
    VirtualWorkspacePathLookup,
    VirtualWorkspaceSourceProjection,
    VirtualWorkspaceSourceProjectionCache,
)
from openhcs.core.step_dependencies import StepInputDependency
from openhcs.core.steps.function_execution import (
    FunctionStepExecutor,
)
from openhcs.core.steps.function_output_identity import (
    FunctionOutputIdentity,
    FunctionOutputIdentityCache,
    FunctionOutputPathRequest,
)
from openhcs.core.steps.function_output_manifest import (
    NoStepOutputManifestMatch,
    ProducedOutputSemantics,
    ProducedPathRecordIndex,
    StepOutputManifestStore,
)
from openhcs.formats.pattern.pattern_discovery import PatternDiscoveryEngine
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser


def _anchor_executor(
    *, plan, parser, output_manifest, source_workspace_projection_cache
):
    executor = object.__new__(FunctionStepExecutor)
    executor.plan = plan
    executor.context = Mock(
        plate_path=Path("."),
        microscope_handler=SimpleNamespace(
            parser=parser,
            metadata_handler=SimpleNamespace(
                source_workspace_metadata_document=lambda _path: None
            ),
        ),
        filemanager=SimpleNamespace(exists=lambda *_args: False),
        runtime_source_workspace_projection_cache=source_workspace_projection_cache,
        runtime_source_binding_context_cache=RuntimeSourceBindingContextCache(),
    )
    executor.context.runtime_source_workspace_projection_authority = (
        VirtualWorkspaceSourceProjectionAuthority.from_context(
            executor.context, cache=source_workspace_projection_cache,
        )
    )
    if output_manifest is not None:
        _STEP_OUTPUT_MANIFESTS[executor.context] = output_manifest
    return executor


def _source_manifest(plan, paths_and_components):
    producer = CompiledStepPlan(
        step_index=plan.main_input_dependency.source_step_index,
        step_type="FunctionStep",
        step_scope_id=plan.main_input_dependency.source_step_scope_id,
        step_name="producer",
        pipeline_position=plan.main_input_dependency.source_step_index,
        axis_id=plan.axis_id,
        output_dir=Path("/memory"),
    )
    parser = SourceSchemaFilenameParser()
    records = []
    for path, overrides in paths_and_components:
        components = dict(parser.parse_filename(path).component_wire_mapping())
        components.update(overrides)
        records.append(
            ProducedOutputSemantics.from_output(
                producer,
                producer.output_dir / path,
                FunctionOutputIdentity(
                    component_values=components, extension=".tif", source="test"
                ),
            )
        )
    store = StepOutputManifestStore()
    store.begin_step(producer)
    store.record_outputs(producer, records)
    return store


@composed_image_payload
def _compose_image_domain(image: object) -> object:
    return image


_MAIN_FLOW_MASK_OUTPUT = ArtifactSpec.output("Mask", ImageArtifactType)
_MAIN_FLOW_MASK_INPUT = ArtifactSpec.input(
    "Mask",
    ImageArtifactType,
    parameter_name="mask",
)


@artifact_outputs(_MAIN_FLOW_MASK_OUTPUT)
@numpy_memory
def _produce_mask_for_main_flow_regression(image):
    return image


@artifact_inputs(_MAIN_FLOW_MASK_INPUT)
@numpy_memory
def _consume_source_with_prior_mask(image, mask):
    del mask
    return image


@numpy_memory
def _identity_source_image(image):
    return image


def test_pattern_discovery_uses_authoritative_virtual_source_files(
    tmp_path: Path,
) -> None:
    plate_path = tmp_path / "plate"
    source_files = [
        plate_path / "A01_s001_w1_z001_t001.tif",
        plate_path / "A01_s002_w1_z001_t001.tif",
        plate_path / "B01_s001_w1_z001_t001.tif",
    ]
    engine = PatternDiscoveryEngine(
        SourceSchemaFilenameParser(),
        SimpleNamespace(),
    )

    patterns = engine.auto_detect_patterns_from_files(
        source_files,
        variable_components=[VariableComponents.SITE.value],
        well_filter=["A01"],
    )

    assert patterns == {"A01": ["A01_s{iii}_w1_z001_t001.tif"]}


def test_pattern_discovery_accepts_axis_scoped_source_projection_files(
    tmp_path: Path,
) -> None:
    plate_path = tmp_path / "plate"
    source_files = [
        plate_path / "A01_s001_w1_z001_t001.tif",
    ]
    engine = PatternDiscoveryEngine(
        SourceSchemaFilenameParser(),
        SimpleNamespace(),
    )

    patterns = engine.auto_detect_patterns_from_axis_files(
        source_files,
        axis_id="source_projection_axis",
        variable_components=[],
    )

    assert patterns == {"source_projection_axis": ["A01_s001_w1_z001_t001.tif"]}


def test_virtual_workspace_pipeline_start_files_preserve_virtual_identity(
    tmp_path: Path,
) -> None:
    """Pipeline-start source resolution must not collapse per-well virtual files."""

    plate_path = tmp_path / "plate"
    real_path = tmp_path / "source" / "image.png"
    virtual_a = plate_path / "W001_s001_w1_z001_t001.png"
    virtual_b = plate_path / "W002_s001_w1_z001_t001.png"
    projection = VirtualWorkspaceSourceProjection(
        source_refs_by_virtual_path={
            virtual_a.name: SourcePixelRef("disk", str(real_path)),
            str(virtual_a): SourcePixelRef("disk", str(real_path)),
            virtual_b.name: SourcePixelRef("disk", str(real_path)),
            str(virtual_b): SourcePixelRef("disk", str(real_path)),
        },
        source_metadata_by_path={
            virtual_a.name: {"well": "W001"},
            virtual_b.name: {"well": "W002"},
        },
        workspace_root=str(plate_path),
    )

    assert projection.pipeline_start_files() == (str(virtual_a), str(virtual_b))
    assert projection.pipeline_start_files(axis_id="W001") == (str(virtual_a),)
    assert projection.pipeline_start_files(axis_id="W002") == (str(virtual_b),)
    assert projection.source_metadata_for(
        VirtualWorkspacePathLookup.from_paths(virtual_a.name, str(virtual_a))
    ) == {"well": "W001"}
    assert projection.source_metadata_for(
        VirtualWorkspacePathLookup.from_paths(virtual_b.name, str(virtual_b))
    ) == {"well": "W002"}


def test_workspace_source_files_select_exact_projection_roles(
    tmp_path: Path,
) -> None:
    plate_path = tmp_path / "plate"
    canonical_path = "A01_s001_w1_z001_t001.tif"
    artifact_path = f"_source/Illumination/{canonical_path}"
    address = OpenHCSPlaneAddress.from_values(
        well="A01",
        site="1",
        channel="1",
        z_index="1",
        timepoint="1",
    )
    plane_projection = SourcePlaneProjection(
        address=address,
        ref=SourcePixelRef("disk", "/source/image.tif"),
        source_alias="Original",
    )
    artifact_projection = SourceArtifactProjection(
        address=address,
        ref=SourcePixelRef("disk", "/source/illumination.npy"),
        source_alias="Illumination",
        artifact_kind=ImageArtifactType,
    )
    projection = VirtualWorkspaceSourceProjection(
        source_refs_by_virtual_path={
            canonical_path: plane_projection.ref,
            artifact_path: artifact_projection.ref,
        },
        source_metadata_by_path={},
        source_projections_by_virtual_path={
            canonical_path: plane_projection,
            artifact_path: artifact_projection,
        },
        workspace_root=str(plate_path),
    )

    assert projection.files_for_projection_role(SourceProjectionRole.PRIMARY_PLANE) == (
        str(plate_path / canonical_path),
    )
    assert projection.files_for_projection_role(
        SourceProjectionRole.SOURCE_ARTIFACT
    ) == (str(plate_path / artifact_path),)


def test_workspace_logical_identity_requires_paired_projection_declaration(
    tmp_path: Path,
) -> None:
    path = "A01_s001_w1_z001_t001.tif"
    full_path = str(tmp_path / path)
    first = SourcePlaneProjection(
        address=OpenHCSPlaneAddress.from_values("A01", 1, 1, 1, 1),
        ref=SourcePixelRef("disk", "/physical/shared.tif"),
        source_alias="Original",
    )
    declarations = {path: first, full_path: first}
    projection = VirtualWorkspaceSourceProjection(
        source_refs_by_virtual_path={path: first.ref, full_path: first.ref},
        source_metadata_by_path={},
        source_projections_by_virtual_path=declarations,
        workspace_root=str(tmp_path),
    )
    lookup = VirtualWorkspacePathLookup.from_paths(full_path, full_path)
    assert projection.logical_path_for(lookup) == path

    # Sharing a backend reference does not prove a shared logical declaration.
    declarations[full_path] = replace(
        first, address=OpenHCSPlaneAddress.from_values("B01", 1, 1, 1, 1)
    )
    assert projection.logical_path_for(lookup) == full_path
    assert projection.source_path_for(lookup) == "/physical/shared.tif"


def test_workspace_source_projection_carries_exact_aliases_into_stack_provenance(
    tmp_path: Path,
) -> None:
    workspace_root = tmp_path / "workspace"
    source_paths = (
        tmp_path / "source" / "raw.tif",
        tmp_path / "source" / "illum.mat",
    )
    projection_set = SourceProjectionSet(
        tuple(
            SourcePlaneProjection(
                address=OpenHCSPlaneAddress.from_values(
                    well="A01",
                    site="1",
                    channel=str(channel),
                    z_index="1",
                    timepoint="1",
                ),
                ref=SourcePixelRef("disk", str(source_path)),
                source_alias=alias,
            )
            for channel, alias, source_path in zip(
                (1, 2),
                ("Raw", "Illum"),
                source_paths,
                strict=True,
            )
        )
    )
    subdirectory = projection_set.metadata_dict(
        parser=SourceSchemaFilenameParser(),
        microscope_handler_name="source_bindings",
        source_filename_parser_name="SourceSchemaFilenameParser",
        grid_dimensions=[1, 1],
        pixel_size=1.0,
    )
    projection = VirtualWorkspaceSourceProjection.from_openhcs_metadata(
        workspace_root,
        {"subdirectories": {".": subdirectory}},
    )

    lookups = tuple(
        VirtualWorkspacePathLookup.from_paths(
            virtual_path,
            str(workspace_root / virtual_path),
        )
        for virtual_path in subdirectory["image_files"]
    )
    projected_payloads = tuple(
        projection.project_payload(
            lookup,
            ImagePayloadMetadata.for_array_payload(
                np.full((4, 5), channel, dtype=np.float32),
                source_path=str(source_path),
            ).payload_with(np.full((4, 5), channel, dtype=np.float32)),
        )
        for channel, source_path, lookup in zip(
            (1, 2),
            source_paths,
            lookups,
            strict=True,
        )
    )

    assert tuple(
        projection.require_source_projection_for(
            VirtualWorkspacePathLookup.from_paths(
                virtual_path,
                str(workspace_root / virtual_path),
            )
        ).source_alias
        for virtual_path in subdirectory["image_files"]
    ) == ("Raw", "Illum")
    assert tuple(
        image_payload_metadata(payload).source_image_names
        for payload in projected_payloads
    ) == (("Raw",), ("Illum",))
    assert all(
        "source_alias"
        not in (image_payload_metadata(payload).source_component_metadata or {})
        for payload in projected_payloads
    )

    stack = stack_image_payloads(
        projected_payloads,
        metadata_mode=projection.payload_composition_mode(lookups),
    )

    assert image_payload_metadata(stack).source_image_names == ("Raw", "Illum")
    assert image_payload_metadata(stack).plane_axis is RuntimePlaneAxis.SOURCE_BINDING


def test_workspace_replay_preserves_collapsed_semantic_identity(
    tmp_path: Path,
) -> None:
    workspace_root = tmp_path / "workspace"
    source_paths = tuple(
        tmp_path / "source" / f"A14_s{site:03d}_w1_z001_t001.tif" for site in (1, 2)
    )
    persisted_metadata = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=tuple(str(path) for path in source_paths),
            component_metadata=tuple(
                {
                    "well": "A14",
                    "site": site,
                    "channel": 1,
                    "z_index": 1,
                    "timepoint": 1,
                }
                for site in (1, 2)
            ),
        ),
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    ).collapse_leading_plane_axis()
    projection_set = SourceProjectionSet(
        (
            SourcePlaneProjection(
                address=OpenHCSPlaneAddress.from_values("A14", 1, 1, 1, 1),
                ref=SourcePixelRef("disk", "/outputs/A14_mosaic.tif"),
                source_alias="neurite",
                image_metadata=persisted_metadata,
            ),
        )
    )
    subdirectory = projection_set.metadata_dict(
        parser=SourceSchemaFilenameParser(),
        microscope_handler_name="source_bindings",
        source_filename_parser_name="SourceSchemaFilenameParser",
        grid_dimensions=[1, 1],
        pixel_size=1.0,
    )
    projection = VirtualWorkspaceSourceProjection.from_openhcs_metadata(
        workspace_root,
        {"subdirectories": {".": subdirectory}},
    )
    virtual_path = subdirectory["image_files"][0]
    projected = projection.project_payload(
        VirtualWorkspacePathLookup.from_paths(
            virtual_path,
            str(workspace_root / virtual_path),
        ),
        ImagePayloadMetadata.for_array_payload(
            np.zeros((4, 5), dtype=np.float32),
            source_path="/outputs/A14_mosaic.tif",
        ).payload_with(np.zeros((4, 5), dtype=np.float32)),
    )

    replayed_metadata = image_payload_metadata(projected)
    semantic_components = replayed_metadata.source_component_metadata
    assert semantic_components is not None
    assert "site" not in semantic_components
    assert replayed_metadata.source_image_names == ("neurite",)
    assert replayed_metadata.source_provenance.source_plane_count == 0
    assert (
        replayed_metadata.source_provenance.source_image_provenance_planes.contributor_count
        == 2
    )
    assert {
        contributor.source_identity.component_metadata["site"]
        for contributor in replayed_metadata.source_provenance.source_image_provenance_planes.contributors
    } == {1, 2}


@pytest.mark.parametrize(
    "source_binding_plan",
    (
        CompiledSourceBindingPlan.empty(),
        CompiledSourceBindingPlan(bindings=(NamedSourceBinding(alias="OrigBlue"),)),
    ),
)
def test_workspace_source_loading_preserves_declared_tiff_intensity_scale(
    tmp_path: Path,
    source_binding_plan: CompiledSourceBindingPlan,
) -> None:
    import tifffile

    from openhcs.core.steps.function_runtime import PatternGroupExecutionRequest

    source_path = tmp_path / "source.tif"
    source_pixels = np.array([[0, 4095]], dtype=np.uint16)
    tifffile.imwrite(
        source_path,
        source_pixels,
        extratags=((281, "H", 1, 4095, False),),
    )
    virtual_path = "A01_s001_w1_z001_t001.tif"
    source_plane = SourcePlaneProjection(
        address=OpenHCSPlaneAddress.from_values(
            well="A01",
            site="1",
            channel="1",
            z_index="1",
            timepoint="1",
        ),
        ref=SourcePixelRef("disk", str(source_path)),
        source_alias="OrigBlue",
    )
    projection = VirtualWorkspaceSourceProjection(
        source_refs_by_virtual_path={virtual_path: source_plane.ref},
        source_metadata_by_path={
            virtual_path: {SOURCE_BINDING_ALIAS_METADATA_FIELD: "OrigBlue"}
        },
        source_projections_by_virtual_path={virtual_path: source_plane},
        workspace_root=str(tmp_path),
    )

    class SourceFileManager:
        @staticmethod
        def resolve_address(backend_address, backend, *, base_path):
            assert backend == "disk"
            assert Path(backend_address) == source_path
            assert Path(base_path) == source_path.parent
            return backend_address

        physical_source_path = resolve_address

    runtime = PatternGroupExecutionRequest(
        context=SimpleNamespace(filemanager=SourceFileManager()),
        execution_plan=CompiledStepPlan(
            step_index=0,
            step_name="source fixture",
            step_type="FunctionStep",
            axis_id="A01",
            source_binding_plan=source_binding_plan,
        ),
        compiled_group=compile_function_pattern(
            lambda image: image, {}, {}
        ).default_group,
        pattern_group_info="fixture",
        component_index=0,
        component_count=1,
    )

    payload = runtime._apply_workspace_source_binding_payload(
        source_pixels,
        source_projection=projection,
        lookup=VirtualWorkspacePathLookup.from_paths(
            virtual_path,
            str(tmp_path / virtual_path),
        ),
    )

    metadata = image_payload_metadata(payload)
    assert metadata.intensity_scale == 4095.0
    assert metadata.source_dtype == "uint16"
    assert metadata.source_image_names == ("OrigBlue",)


def test_physical_source_loading_preserves_tiff_calibration_and_live_buffers(
    tmp_path: Path,
) -> None:
    import tifffile
    from polystore.base import ensure_storage_registry, storage_registry
    from polystore.filemanager import FileManager

    from openhcs.constants.constants import Backend
    from openhcs.core.runtime_image_values import image_payload_mask
    from openhcs.core.runtime_source_binding_cache import (
        RuntimeSourceBindingContextCache,
    )
    from openhcs.core.steps.function_runtime import PatternGroupExecutionRequest
    from openhcs.microscopes.source_schema import SourceSchemaFilenameParser

    source_path = tmp_path / "A01_s002_w1_z003_t004.tif"
    pixels = np.array([[0, 4095]], dtype=np.uint16)
    mask = np.array([[True, False]])
    tifffile.imwrite(source_path, pixels, extratags=((281, "H", 1, 4095, False),))
    ensure_storage_registry()
    filemanager = FileManager(dict(storage_registry))
    bindings = CompiledSourceBindingPlan.empty()
    plan = CompiledStepPlan(
        step_index=0,
        step_name="Physical source",
        step_type="FunctionStep",
        axis_id="A01",
        input_dir=tmp_path,
        output_dir=tmp_path / "outputs",
        output_plate_root=tmp_path / "outputs",
        sub_dir="images",
        read_backend=Backend.DISK.value,
        write_backend=Backend.MEMORY.value,
        pipeline_position=0,
        variable_components=(),
        source_binding_plan=bindings,
        compiled_function_pattern=compile_function_pattern(lambda image: image, {}, {}),
    )
    context = SimpleNamespace(
        input_dir=tmp_path,
        filemanager=filemanager,
        microscope_handler=SimpleNamespace(
            parser=SourceSchemaFilenameParser(),
            get_primary_backend=lambda *_args: Backend.DISK.value,
        ),
        runtime_source_binding_context_cache=RuntimeSourceBindingContextCache(),
    )
    runtime = PatternGroupExecutionRequest(
        context=context,
        execution_plan=replace(plan, source_binding_plan=bindings),
        compiled_group=compile_function_pattern(
            lambda image: image, {}, {}
        ).default_group,
        pattern_group_info="fixture",
        component_index=0,
        component_count=1,
    )
    payload = ImagePayloadMetadata().payload_with(pixels, mask)
    lookup = VirtualWorkspacePathLookup.from_paths(source_path.name, str(source_path))

    (loaded,) = runtime._apply_source_image_loading_semantics(
        (payload,),
        (lookup,),
        (),
        None,
    )

    metadata = image_payload_metadata(loaded)
    assert metadata.intensity_scale == 4095.0
    assert metadata.source_dtype == "uint16"
    assert metadata.source_path == str(source_path)
    assert metadata.source_component_metadata["site"] == 2
    assert metadata.source_component_metadata["z_index"] == 3
    assert metadata.source_component_metadata["timepoint"] == 4
    assert image_payload_data(loaded) is pixels
    assert image_payload_mask(loaded) is mask
    np.testing.assert_array_equal(image_payload_data(loaded), [[0, 4095]])
    pixels[0, 0] = 17
    mask[0, 0] = False
    assert image_payload_data(loaded)[0, 0] == 17
    assert not image_payload_mask(loaded)[0, 0]


def test_virtual_workspace_source_filters_use_persisted_candidate_identity(
    tmp_path: Path,
) -> None:
    plate_path = tmp_path / "plate"
    virtual_paths = (
        plate_path / "A01_s001_w1_z001_t001.tif",
        plate_path / "A01_s002_w1_z001_t001.tif",
    )
    source_filter_paths = (
        tmp_path / "source" / "0_1_N_R.png",
        tmp_path / "source" / "0_2_N_R.png",
    )
    source_metadata_by_path: dict[str, dict[str, object]] = {}
    for site, (virtual_path, source_filter_path) in enumerate(
        zip(virtual_paths, source_filter_paths, strict=True),
        start=1,
    ):
        filter_metadata: dict[str, object] = {"site": str(site)}
        SourceFilterPathMetadata.from_paths((str(source_filter_path),)).merge_into(
            filter_metadata,
            path=virtual_path.name,
        )
        source_metadata_by_path[virtual_path.name] = filter_metadata
        source_metadata_by_path[str(virtual_path)] = filter_metadata
    source_ref = SourcePixelRef(
        "opaque_backend",
        '{"opaque":"address-without-source-name"}',
    )
    projection = VirtualWorkspaceSourceProjection(
        source_refs_by_virtual_path={
            path_key: source_ref
            for virtual_path in virtual_paths
            for path_key in (virtual_path.name, str(virtual_path))
        },
        source_metadata_by_path=source_metadata_by_path,
        workspace_root=str(plate_path),
    )
    context = SourcePatternResolutionContext.from_projection(
        parser=SourceSchemaFilenameParser(),
        projection=projection,
    )

    assert context.candidate_filter_paths(str(virtual_paths[0])) == (
        str(source_filter_paths[0]),
    )
    assert context.candidate_filter_paths("A01_s{iii}_w1_z001_t001.tif") == (
        str(source_filter_paths[0]),
        str(source_filter_paths[1]),
    )


def test_virtual_workspace_axis_filter_uses_virtual_filename_metadata_when_missing(
    tmp_path: Path,
) -> None:
    plate_path = tmp_path / "plate"
    real_path = tmp_path / "source" / "image.png"
    virtual_a = plate_path / "A01_s001_w1_z001_t001.tif"
    virtual_b = plate_path / "A02_s001_w1_z001_t001.tif"
    projection = VirtualWorkspaceSourceProjection(
        source_refs_by_virtual_path={
            virtual_a.name: SourcePixelRef("disk", str(real_path)),
            virtual_b.name: SourcePixelRef("disk", str(real_path)),
        },
        source_metadata_by_path={},
        workspace_root=str(plate_path),
    )

    assert projection.pipeline_start_files(axis_id="A01") == (str(virtual_a),)
    assert projection.pipeline_start_files(axis_id="A02") == (str(virtual_b),)
    assert projection.source_metadata_for(
        VirtualWorkspacePathLookup.from_paths(virtual_a.name, str(virtual_a))
    ) == {
        "well": "A01",
        "site": 1,
        "channel": 1,
        "z_index": 1,
        "timepoint": 1,
        "extension": ".tif",
    }


def test_virtual_workspace_runtime_metadata_projection_validates_explicit_metadata(
    tmp_path: Path,
) -> None:
    plate_path = tmp_path / "plate"
    real_path = tmp_path / "source" / "image.tif"
    virtual_path = plate_path / "A01_s001_w1_z001_t001.tif"
    projection = VirtualWorkspaceSourceProjection(
        source_refs_by_virtual_path={
            virtual_path.name: SourcePixelRef("disk", str(real_path)),
            str(virtual_path): SourcePixelRef("disk", str(real_path)),
        },
        source_metadata_by_path={
            virtual_path.name: {"OpenHCSSourceVoxelSpacingZYX": "2,1,1"},
            str(virtual_path): {"OpenHCSSourceVoxelSpacingZYX": "2,1,1"},
        },
        workspace_root=str(plate_path),
    )

    projection.validate_runtime_metadata_projection()
    # Compile validation uses the already-admitted view, without a runtime
    # context/provider capable of reopening the source document.
    PipelineCompiler.validate_source_workspace_projection(
        SimpleNamespace(source_workspace_projection=projection, axis_id="A01")
    )


@pytest.mark.parametrize("field_name", ("OpenHCSSourceVoxelSpacingZYX", "well"))
def test_virtual_workspace_runtime_metadata_projection_rejects_path_spelling_drift(
    tmp_path: Path,
    field_name: str,
) -> None:
    plate_path = tmp_path / "plate"
    real_path = tmp_path / "source" / "image.tif"
    virtual_path = plate_path / "A01_s001_w1_z001_t001.tif"
    projection = VirtualWorkspaceSourceProjection(
        source_refs_by_virtual_path={
            virtual_path.name: SourcePixelRef("disk", str(real_path)),
        },
        source_metadata_by_path={
            virtual_path.name: {field_name: "A01" if field_name == "well" else "2,1,1"},
            **({str(virtual_path): {"well": "A02"}} if field_name == "well" else {}),
        },
        workspace_root=str(plate_path),
    )

    with pytest.raises(ValueError, match=field_name):
        projection.validate_runtime_metadata_projection()
    with pytest.raises(ValueError, match=field_name):
        PipelineCompiler.validate_source_workspace_projection(
            SimpleNamespace(source_workspace_projection=projection, axis_id="A01")
        )
    if field_name == "well":
        PipelineCompiler.validate_source_workspace_projection(
            SimpleNamespace(source_workspace_projection=projection, axis_id="A02")
        )
    else:
        # Metadata without an axis remains shared by every admitted axis.
        with pytest.raises(ValueError, match=field_name):
            PipelineCompiler.validate_source_workspace_projection(
                SimpleNamespace(source_workspace_projection=projection, axis_id="A02")
            )


def test_stack_payload_context_promotes_single_channel_slice_metadata() -> None:
    first = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/input/A01_s001_w1_z001_t001.tif",),
            component_metadata=({"well": "A01", "site": 1, "channel": 1},),
        )
    ).payload_with(np.zeros((4, 5), dtype=np.float32), None)
    second = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/input/A01_s002_w1_z001_t001.tif",),
            component_metadata=({"well": "A01", "site": 2, "channel": 1},),
        )
    ).payload_with(np.ones((4, 5), dtype=np.float32), None)
    stack = np.stack(
        (
            image_payload_data(first),
            image_payload_data(second),
        )
    )

    payload = stack_image_payloads(
        (first, second),
        metadata_mode=ImagePayloadMetadataCompositionMode.STACK,
    )
    metadata = image_payload_metadata(payload)

    assert metadata.source_image_provenance_planes.paths == (
        "/input/A01_s001_w1_z001_t001.tif",
        "/input/A01_s002_w1_z001_t001.tif",
    )
    assert tuple(
        dict(item)
        for item in metadata.source_image_provenance_planes.component_metadata
    ) == (
        {"well": "A01", "site": 1, "channel": 1},
        {"well": "A01", "site": 2, "channel": 1},
    )


@pytest.mark.parametrize("extension", (None, ".tif", ".png"))
def test_bundle_payload_context_preserves_source_binding_plane_metadata(
    extension: str | None,
) -> None:
    # Consensus preserves declared metadata; it must not parse the TIFF paths.
    extension_metadata = {} if extension is None else {"extension": extension}
    first = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/input/A01_s001_w1_z001_t001.tif",),
            component_metadata=(
                {"well": "A01", "site": 1, "channel": 1, **extension_metadata},
            ),
        )
    ).payload_with(np.zeros((4, 5), dtype=np.float32), None)
    second = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/input/A01_s001_w2_z001_t001.tif",),
            component_metadata=(
                {"well": "A01", "site": 1, "channel": 2, **extension_metadata},
            ),
        )
    ).payload_with(np.ones((4, 5), dtype=np.float32), None)

    bundle = ImagePayloadBundleContext.from_payloads((first, second)).compose()
    metadata = image_payload_metadata(bundle)

    assert metadata.source_image_provenance_planes.paths == (
        "/input/A01_s001_w1_z001_t001.tif",
        "/input/A01_s001_w2_z001_t001.tif",
    )
    assert tuple(
        dict(item)
        for item in metadata.source_image_provenance_planes.component_metadata
    ) == (
        {"well": "A01", "site": 1, "channel": 1, **extension_metadata},
        {"well": "A01", "site": 1, "channel": 2, **extension_metadata},
    )
    assert dict(metadata.source_component_metadata) == {
        "well": "A01",
        "site": 1,
        **extension_metadata,
    }


def test_payload_slices_do_not_infer_alignment_from_source_provenance() -> None:
    metadata = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("grayscale.tif", "color.tif"),
            component_metadata=(
                {"site": "1"},
                {"site": "2"},
            ),
        )
    )
    payload = metadata.payload_with(np.zeros((2, 4, 5), dtype=np.float32))

    slices = payload_slices_for_alignment(payload)

    assert len(slices) == 1
    assert slices[0] is payload


def test_step_output_manifest_scopes_previous_step_inputs(tmp_path: Path) -> None:
    output_dir = tmp_path / "images"
    producer = CompiledStepPlan(
        step_index=1,
        step_type="FunctionStep",
        step_scope_id="enhance",
        step_name="Enhance",
        pipeline_position=1,
        axis_id="A14",
        output_dir=output_dir,
    )
    consumer = SimpleNamespace(
        axis_id="A14",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=3,
            source_step_scope_id="enhance",
        ),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
        artifact_inputs={},
        compiled_function_pattern=compile_function_pattern(lambda image: image, {}, {}),
    )
    store = StepOutputManifestStore()

    store.begin_step(producer)
    store.record_outputs(
        producer,
        [
            ProducedOutputSemantics.from_output(
                producer,
                output_dir / "A14_s001_w1_z001_t001.tif",
                FunctionOutputIdentity(
                    component_values={
                        "well": "A14",
                        "site": 1,
                        "channel": 1,
                        "z_index": 1,
                        "timepoint": 1,
                    },
                    extension=".tif",
                    source="test",
                ),
            )
        ],
    )
    store.begin_step(producer)
    store.record_outputs(
        producer,
        [
            ProducedOutputSemantics.from_output(
                producer,
                output_dir / "A14_s001_w3_z001_t001.tif",
                FunctionOutputIdentity(
                    component_values={
                        "well": "A14",
                        "site": 1,
                        "channel": 3,
                        "z_index": 1,
                        "timepoint": 1,
                    },
                    extension=".tif",
                    source="test",
                ),
            ),
            ProducedOutputSemantics.from_output(
                producer,
                output_dir / "A14_s002_w3_z001_t001.tif",
                FunctionOutputIdentity(
                    component_values={
                        "well": "A14",
                        "site": 2,
                        "channel": 3,
                        "z_index": 1,
                        "timepoint": 1,
                    },
                    extension=".tif",
                    source="test",
                ),
            ),
        ],
    )

    assert store.producer_paths_for(consumer) == (
        "A14_s001_w3_z001_t001.tif",
        "A14_s002_w3_z001_t001.tif",
    )


def test_step_output_manifest_pattern_lookup_returns_producer_memory_paths(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "images"
    producer = CompiledStepPlan(
        step_index=4,
        step_type="FunctionStep",
        step_scope_id="mask_image",
        step_name="MaskImage",
        pipeline_position=4,
        axis_id="A14",
        output_dir=output_dir,
    )
    consumer = SimpleNamespace(
        axis_id="A14",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=4,
            source_step_scope_id="mask_image",
        ),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
        artifact_inputs={},
        compiled_function_pattern=compile_function_pattern(lambda image: image, {}, {}),
    )
    store = StepOutputManifestStore()

    store.begin_step(producer)
    store.record_outputs(
        producer,
        (
            ProducedOutputSemantics.from_output(
                producer,
                output_dir / "A14_s001_w3_z001_t001.tif",
                FunctionOutputIdentity(
                    component_values={
                        "well": "A14",
                        "site": 1,
                        "channel": 3,
                        "z_index": 1,
                        "timepoint": 1,
                    },
                    extension=".tif",
                    source="test",
                ),
            ),
            ProducedOutputSemantics.from_output(
                producer,
                output_dir / "A14_s002_w3_z001_t001.tif",
                FunctionOutputIdentity(
                    component_values={
                        "well": "A14",
                        "site": 2,
                        "channel": 3,
                        "z_index": 1,
                        "timepoint": 1,
                    },
                    extension=".tif",
                    source="test",
                ),
            ),
        ),
    )

    index = store.producer_record_index_for(consumer, SourceSchemaFilenameParser())
    assert [record.output_path for record in index.matching_records(
        "A14_s{iii}_w3_z001_t001.tif"
    )] == [
        str(output_dir / "A14_s001_w3_z001_t001.tif"),
        str(output_dir / "A14_s002_w3_z001_t001.tif"),
    ]


def test_step_output_manifest_does_not_treat_artifact_inputs_as_main_flow(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "images"
    cells_producer = CompiledStepPlan(
        step_index=6,
        step_type="FunctionStep",
        step_scope_id="identify_cells",
        step_name="IdentifySecondaryObjects",
        pipeline_position=6,
        axis_id="A14",
        output_dir=output_dir,
    )
    nuclei_producer = CompiledStepPlan(
        step_index=5,
        step_type="FunctionStep",
        step_scope_id="identify_nuclei",
        step_name="IdentifyPrimaryObjects",
        pipeline_position=5,
        axis_id="A14",
        output_dir=output_dir,
    )
    consumer = SimpleNamespace(
        axis_id="A14",
        main_input_dependency=StepInputDependency.pipeline_start(),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
        artifact_inputs={
            plan.ref(): plan
            for plan in (
                ArtifactInputPlan(
                    name="Cells",
                    path="Cells",
                    artifact_type=ObjectLabelsArtifactType,
                    source_step_id=6,
                    source_step_scope_id="identify_cells",
                ),
                ArtifactInputPlan(
                    name="Nuclei",
                    path="Nuclei",
                    artifact_type=ObjectLabelsArtifactType,
                    source_step_id=5,
                    source_step_scope_id="identify_nuclei",
                ),
            )
        },
        compiled_function_pattern=compile_function_pattern(lambda image: image, {}, {}),
    )
    store = StepOutputManifestStore()

    for producer, output_key in (
        (cells_producer, "Cells"),
        (nuclei_producer, "Nuclei"),
    ):
        store.begin_step(producer)
        store.record_outputs(
            producer,
            (
                ProducedOutputSemantics.from_output(
                    producer,
                    output_dir / "A14_s001_w1_z001_t001.tif",
                    FunctionOutputIdentity(
                        component_values={
                            "well": "A14",
                            "site": 1,
                            "channel": 1,
                            "z_index": 1,
                            "timepoint": 1,
                        },
                        extension=".tif",
                        source="test",
                    ),
                    output_context=AlignedImageSliceContext.main_flow(
                        output_key=output_key,
                        artifact_kind=ObjectLabelsArtifactType.value,
                    ),
                ),
                ProducedOutputSemantics.from_output(
                    producer,
                    output_dir / "A14_s002_w1_z001_t001.tif",
                    FunctionOutputIdentity(
                        component_values={
                            "well": "A14",
                            "site": 2,
                            "channel": 1,
                            "z_index": 1,
                            "timepoint": 1,
                        },
                        extension=".tif",
                        source="test",
                    ),
                    output_context=AlignedImageSliceContext.main_flow(
                        output_key=output_key,
                        artifact_kind=ObjectLabelsArtifactType.value,
                    ),
                ),
            ),
        )

    index = store.producer_record_index_for(consumer, SourceSchemaFilenameParser())
    assert index is None


def test_step_output_manifest_uses_declared_artifact_producer_scope(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "images"
    requested_producer = CompiledStepPlan(
        step_index=2,
        step_type="FunctionStep",
        step_scope_id="crop_blue",
        step_name="CropBlue",
        pipeline_position=2,
        axis_id="A01",
        output_dir=output_dir,
    )
    previous_producer = CompiledStepPlan(
        step_index=3,
        step_type="FunctionStep",
        step_scope_id="crop_red",
        step_name="CropRed",
        pipeline_position=3,
        axis_id="A01",
        output_dir=output_dir,
    )
    consumer = SimpleNamespace(
        axis_id="A01",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=3,
            source_step_scope_id="crop_red",
        ),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
        artifact_inputs={
            plan.ref(): plan
            for plan in (
                ArtifactInputPlan(
                    name="CropBlue",
                    path="CropBlue",
                    artifact_type=ImageArtifactType,
                    source_step_id=2,
                    source_step_scope_id="crop_blue",
                ),
            )
        },
        compiled_function_pattern=compile_function_pattern(lambda image: image, {}, {}),
    )
    store = StepOutputManifestStore()

    store.begin_step(requested_producer)
    store.record_outputs(
        requested_producer,
        (
            ProducedOutputSemantics.from_output(
                requested_producer,
                output_dir / "A01_s001_w1_z001_t001.tif",
                FunctionOutputIdentity(
                    component_values={
                        "well": "A01",
                        "site": 1,
                        "channel": 1,
                        "z_index": 1,
                        "timepoint": 1,
                    },
                    extension=".tif",
                    source="test",
                ),
                output_context=AlignedImageSliceContext.main_flow(
                    output_key="CropBlue",
                    artifact_kind=ImageArtifactType.value,
                ),
            ),
        ),
    )
    store.begin_step(previous_producer)
    store.record_outputs(
        previous_producer,
        (
            ProducedOutputSemantics.from_output(
                previous_producer,
                output_dir / "A01_s001_w2_z001_t001.tif",
                FunctionOutputIdentity(
                    component_values={
                        "well": "A01",
                        "site": 1,
                        "channel": 2,
                        "z_index": 1,
                        "timepoint": 1,
                    },
                    extension=".tif",
                    source="test",
                ),
                output_context=AlignedImageSliceContext.main_flow(
                    output_key="CropRed",
                    artifact_kind=ImageArtifactType.value,
                ),
            ),
        ),
    )

    assert store.filter_to_producer_paths(
        consumer,
        [
            "A01_s001_w1_z001_t001.tif",
            "A01_s001_w2_z001_t001.tif",
        ],
        SourceSchemaFilenameParser(),
    ) == ["A01_s001_w2_z001_t001.tif"]


def test_special_artifact_input_does_not_narrow_step_output_main_flow(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "images"
    producer = CompiledStepPlan(
        step_index=2,
        step_type="FunctionStep",
        step_scope_id="image_set",
        step_name="ImageSet",
        pipeline_position=2,
        axis_id="A01",
        output_dir=output_dir,
    )
    consumer = SimpleNamespace(
        axis_id="A01",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=2,
            source_step_scope_id="image_set",
        ),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
        artifact_inputs={
            plan.ref(): plan
            for plan in (
                ArtifactInputPlan(
                    name="Objects",
                    path="Objects",
                    artifact_type=ObjectLabelsArtifactType,
                    source_step_id=2,
                    source_step_scope_id="image_set",
                ),
            )
        },
        compiled_function_pattern=compile_function_pattern(lambda image: image, {}, {}),
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
            for channel, output_key in ((1, "Image1"), (2, "Image2"))
        ),
    )

    assert store.filter_to_producer_paths(
        consumer,
        [
            "A01_s001_w1_z001_t001.tif",
            "A01_s001_w2_z001_t001.tif",
        ],
        SourceSchemaFilenameParser(),
    ) == [
        "A01_s001_w1_z001_t001.tif",
        "A01_s001_w2_z001_t001.tif",
    ]


def test_step_output_manifest_ignores_sidecar_artifact_for_anchor_filtering() -> None:
    consumer = SimpleNamespace(
        axis_id="A01",
        main_input_dependency=StepInputDependency.pipeline_start(),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
        artifact_inputs={
            plan.ref(): plan
            for plan in (
                ArtifactInputPlan(
                    name="CropBlue__crop_mask",
                    path="CropBlue__crop_mask",
                    artifact_type=ImageArtifactType,
                    sidecar_role=ArtifactSidecarRole.CROP_MASK,
                    source_step_id=0,
                    source_step_scope_id="crop_mask",
                ),
            )
        },
        compiled_function_pattern=compile_function_pattern(lambda image: image, {}, {}),
    )

    assert StepOutputManifestStore().filter_to_producer_paths(
        consumer,
        ["A01_s{iii}_w2_z001_t001.tif"],
        SourceSchemaFilenameParser(),
    ) == ["A01_s{iii}_w2_z001_t001.tif"]


def test_step_output_manifest_preserves_pipeline_start_source_bound_anchor() -> None:
    consumer = SimpleNamespace(
        axis_id="A14",
        main_input_dependency=StepInputDependency.pipeline_start(),
        source_binding_plan=CompiledSourceBindingPlan(
            bindings=(NamedSourceBinding(alias="OrigActin_Golgi_Membrane"),)
        ),
        artifact_inputs={
            plan.ref(): plan
            for plan in (
                ArtifactInputPlan(
                    name="Nuclei",
                    path="Nuclei",
                    artifact_type=ObjectLabelsArtifactType,
                    source_step_id=0,
                    source_step_scope_id="identify_primary",
                ),
            )
        },
        compiled_function_pattern=compile_function_pattern(lambda image: image, {}, {}),
    )

    assert StepOutputManifestStore().filter_to_producer_paths(
        consumer,
        ["A14_s{iii}_w4_z001_t001.tif"],
        SourceSchemaFilenameParser(),
    ) == ["A14_s{iii}_w4_z001_t001.tif"]


def test_step_output_anchor_filter_skips_source_binding_filter() -> None:
    plan = SimpleNamespace(
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=4,
            source_step_scope_id="mask_image",
        ),
        source_binding_plan=CompiledSourceBindingPlan(
            bindings=(NamedSourceBinding(alias="OrigDNA"),)
        ),
    )
    grouped_patterns = {None: ("A14_s{iii}_w1_z001_t001.tif",)}
    pattern_filter = _anchor_executor(
        plan=plan,
        parser=None,
        output_manifest=StepOutputManifestStore(),
        source_workspace_projection_cache=VirtualWorkspaceSourceProjectionCache(),
    )

    assert (
        pattern_filter.source_bound_anchor_patterns(grouped_patterns)
        is grouped_patterns
    )


def test_step_output_anchor_uses_compiler_owned_component_scope() -> None:
    plan = SimpleNamespace(
        axis_id="A01",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=4,
            source_step_scope_id="object_to_image",
        ),
        execution_group_scope=ComponentGroupScope.from_raw(
            ("0",),
            component=AllComponents.CHANNEL,
        ),
        compiled_function_pattern=compile_function_pattern(lambda image: image, {}, {}),
    )
    grouped_patterns = {"2": ("A01_s{iii}_w2_z001_t001.tif",)}
    pattern_filter = _anchor_executor(
        plan=plan,
        parser=SourceSchemaFilenameParser(),
        output_manifest=_source_manifest(
            plan, [("A01_s001_w2_z001_t001.tif", {"channel": 0})]
        ),
        source_workspace_projection_cache=VirtualWorkspaceSourceProjectionCache(),
    )

    assert pattern_filter.execution_group_anchor_patterns(grouped_patterns) == {
        "0": ("A01_s{iii}_w2_z001_t001.tif",),
    }


def test_step_output_dispatch_projects_producer_group_before_pattern_selection(
    monkeypatch,
) -> None:
    def identify_secondary(image):
        return image

    compiled_pattern = compile_function_pattern(
        {"2": identify_secondary},
        {},
        {},
    )
    plan = SimpleNamespace(
        axis_id="A01",
        step_index=4,
        step_name="IdentifySecondaryObjects",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=3,
            source_step_scope_id="identify_primary",
        ),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
        execution_group_value="channel",
        execution_group_scope=ComponentGroupScope.from_raw(
            ("2",),
            component=AllComponents.CHANNEL,
        ),
        compiled_function_pattern=compiled_pattern,
    )
    pattern_filter = _anchor_executor(
        plan=plan,
        parser=SourceSchemaFilenameParser(),
        output_manifest=_source_manifest(
            plan, [("A01_s001_w1_z001_t001.tif", {"channel": 2})]
        ),
        source_workspace_projection_cache=VirtualWorkspaceSourceProjectionCache(),
    )
    executor = pattern_filter

    grouped = executor._prepare_groups({"A01": {"1": ("A01_s{iii}_w1_z001_t001.tif",)}})

    assert grouped == {
        "2": ("A01_s{iii}_w1_z001_t001.tif",),
    }


def test_artifact_managed_dispatch_validates_producer_before_group_projection() -> None:
    runtime_image = ArtifactSpec.input("CropBlue", ImageArtifactType)

    @artifact_inputs(runtime_image)
    @runtime_adapter(
        "runtime",
        lambda _request: object(),
        manages_artifact_inputs=True,
    )
    def identify_primary_objects(image, *, runtime):
        del runtime
        return image

    runtime_plan = ArtifactInputPlan(
        name=runtime_image.name,
        path="/memory/CropBlue.pkl",
        artifact_type=runtime_image.artifact_type,
    )
    compiled_pattern = compile_function_pattern(
        identify_primary_objects,
        {plan.ref(): plan for plan in (runtime_plan,)},
        {},
    )
    compiled_pattern = PathPlannerArtifactStage(
        PathPlanner.__new__(PathPlanner)
    ).compile_invocation_input_edges(
        compiled_pattern,
        artifact_inputs={runtime_plan.ref(): runtime_plan},
        relation_source_scopes={
            runtime_image.ref(): runtime_plan.producer_group_scope(),
        },
        execution_group_scope=ComponentGroupScope.from_raw(
            ("1",),
            component=AllComponents.CHANNEL,
        ),
        consumer_variable_components=ComponentSet(),
    )
    invocation = next(compiled_pattern.iter_invocations())
    assert tuple(edge.spec for edge in invocation.artifact_input_edges) == (
        runtime_image,
    )
    plan = SimpleNamespace(
        axis_id="A01",
        step_index=2,
        step_name="IdentifyPrimaryObjects",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=1,
            source_step_scope_id="crop_green_red",
        ),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
        execution_group_value="channel",
        execution_group_scope=ComponentGroupScope.from_raw(
            ("1",),
            component=AllComponents.CHANNEL,
        ),
        compiled_function_pattern=compiled_pattern,
    )

    def filter_to_producer_paths(_plan, paths, _parser):
        return tuple(path for path in paths if "_w2_" in path)

    pattern_filter = _anchor_executor(
        plan=plan,
        parser=SourceSchemaFilenameParser(),
        output_manifest=SimpleNamespace(
            filter_to_producer_paths=filter_to_producer_paths,
        ),
        source_workspace_projection_cache=VirtualWorkspaceSourceProjectionCache(),
    )

    filtered = pattern_filter._filter_anchor_patterns(
        {
            "1": ("A01_s{iii}_w1_z001_t001.tif",),
            "2": ("A01_s{iii}_w2_z001_t001.tif",),
        }
    )

    assert filtered == {
        "1": ("A01_s{iii}_w2_z001_t001.tif",),
    }


def test_artifact_managed_missing_output_context_is_an_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from openhcs.core.steps import function_runtime

    class MissingProducerManifest:
        def producer_output_contexts_for_paths(self, *_args):
            raise NoStepOutputManifestMatch

    monkeypatch.setattr(
        function_runtime,
        "step_output_manifest",
        lambda _context: MissingProducerManifest(),
    )
    runtime = PatternGroupExecutionRequest(
        context=SimpleNamespace(
            microscope_handler=SimpleNamespace(parser=SourceSchemaFilenameParser())
        ),
        execution_plan=CompiledStepPlan(
            step_index=0,
            step_name="source fixture",
            step_type="FunctionStep",
            axis_id="A01",
        ),
        compiled_group=SimpleNamespace(
            runtime_domain=RuntimeInvocationDomain.ARTIFACT_MANAGED,
        ),
        pattern_group_info="A01_s001_w2_z001_t001.tif",
        component_index=0,
        component_count=1,
    )

    with pytest.raises(NoStepOutputManifestMatch):
        runtime._producer_output_contexts(("A01_s001_w2_z001_t001.tif",))


def test_step_output_anchor_resolves_dynamic_component_scope_from_patterns() -> None:
    plan = SimpleNamespace(
        axis_id="A01",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=4,
            source_step_scope_id="crop",
        ),
        execution_group_scope=ComponentGroupScope.dynamic(AllComponents.SITE),
        compiled_function_pattern=compile_function_pattern(
            lambda image: image,
            {},
            {},
        ),
    )
    grouped_patterns = {
        "1": ("A01_s001_w{iii}_z001_t001.tif",),
        "2": ("A01_s002_w{iii}_z001_t001.tif",),
    }
    pattern_filter = _anchor_executor(
        plan=plan,
        parser=SourceSchemaFilenameParser(),
        output_manifest=_source_manifest(
            plan,
            [
                ("A01_s001_w1_z001_t001.tif", {}),
                ("A01_s002_w1_z001_t001.tif", {}),
            ],
        ),
        source_workspace_projection_cache=VirtualWorkspaceSourceProjectionCache(),
    )

    assert (
        pattern_filter.execution_group_anchor_patterns(grouped_patterns)
        == grouped_patterns
    )


def test_source_anchor_uses_compiler_owned_static_component_scope() -> None:
    plan = SimpleNamespace(
        main_input_dependency=StepInputDependency.pipeline_start(),
        execution_group_scope=ComponentGroupScope.from_raw(
            ("1",),
            component=AllComponents.CHANNEL,
        ),
        compiled_function_pattern=compile_function_pattern(
            lambda image: image,
            {},
            {},
        ),
    )
    grouped_patterns = {
        "1": ("A01_s{iii}_w1_z001_t001.tif",),
        "2": ("A01_s{iii}_w2_z001_t001.tif",),
        "3": ("A01_s{iii}_w3_z001_t001.tif",),
    }
    pattern_filter = _anchor_executor(
        plan=plan,
        parser=None,
        output_manifest=StepOutputManifestStore(),
        source_workspace_projection_cache=VirtualWorkspaceSourceProjectionCache(),
    )

    assert pattern_filter.execution_group_anchor_patterns(grouped_patterns) == {
        "1": ("A01_s{iii}_w1_z001_t001.tif",),
    }


def test_source_bound_anchor_filter_combines_ordered_non_grouped_source_sets() -> None:
    bindings = (
        NamedSourceBinding(
            alias="OrigStain1",
            selector=SourceSelector(
                components=(ComponentSelector(AllComponents.CHANNEL, "1"),),
            ),
            origin=SourceBindingOrigin.PIPELINE_START,
            component_identity=(ComponentSelector(AllComponents.CHANNEL, "1"),),
        ),
        NamedSourceBinding(
            alias="OrigStain2",
            selector=SourceSelector(
                components=(ComponentSelector(AllComponents.CHANNEL, "2"),),
            ),
            origin=SourceBindingOrigin.PIPELINE_START,
            component_identity=(ComponentSelector(AllComponents.CHANNEL, "2"),),
        ),
    )
    source_binding_plan = CompiledSourceBindingPlan(
        bindings=bindings,
        match_plan=SourceBindingMatchPlan(method=SourceBindingMatchMethod.ORDER),
    )

    source_set_measurements = ArtifactSpec.output(
        "SourceSetMeasurements",
        MeasurementsArtifactType,
        relations=tuple(
            GroupLineageSourceRelation(source=binding.input_spec().ref())
            for binding in bindings
        )
        + (ArtifactMeasurementSubjectRelation(),),
    )

    @artifact_inputs(*(binding.input_spec() for binding in bindings))
    @artifact_outputs(source_set_measurements)
    @composed_image_payload
    def measure_source_set(image):
        return image

    measurement_plan = ArtifactOutputPlan(
        name="SourceSetMeasurements",
        path="/memory/SourceSetMeasurements.pkl",
        artifact_type=MeasurementsArtifactType,
        group_keys=("1", "2"),
        group_component=AllComponents.CHANNEL,
        relations=source_set_measurements.relations,
    )

    plan = SimpleNamespace(
        axis_id="A01",
        step_index=0,
        step_name="SourceBoundAnchorFilter",
        main_input_dependency=StepInputDependency.pipeline_start(),
        source_binding_plan=source_binding_plan,
        execution_group_scope=ComponentGroupScope.from_raw(
            ("1", "2"),
            component=AllComponents.CHANNEL,
        ),
        compiled_function_pattern=compile_function_pattern(
            measure_source_set,
            {},
            {plan.ref(): plan for plan in (measurement_plan,)},
        ),
    )
    pattern_filter = _anchor_executor(
        plan=plan,
        parser=SourceSchemaFilenameParser(),
        output_manifest=StepOutputManifestStore(),
        source_workspace_projection_cache=VirtualWorkspaceSourceProjectionCache(),
    )

    filtered = pattern_filter.source_bound_anchor_patterns(
        {
            "1": (
                "A01_s001_w1_z001_t001.tif",
                "A01_s002_w1_z001_t001.tif",
            ),
            "2": (
                "A01_s001_w2_z001_t001.tif",
                "A01_s002_w2_z001_t001.tif",
            ),
            "3": ("A01_s001_w3_z001_t001.tif",),
        }
    )

    assert filtered == {
        "1": (
            "A01_s001_w1_z001_t001.tif",
            "A01_s002_w1_z001_t001.tif",
        ),
        "2": (),
        "3": (),
    }


def test_callable_contract_source_inputs_project_bindings_through_exact_ref_authority() -> (
    None
):
    source_spec = ArtifactSpec.input("OrigBlue", ImageArtifactType)

    @artifact_inputs(source_spec)
    @runtime_adapter("runtime", lambda _request: object())
    def exact_source_input(image, *, runtime):
        del runtime
        return image

    compiled_group = compile_function_pattern(
        exact_source_input,
        {},
        {},
    ).default_group
    source_binding_plan = CompiledSourceBindingPlan(
        bindings=(
            NamedSourceBinding(alias="OrigBlue"),
            NamedSourceBinding(alias="OrigGreen"),
        )
    )

    invocation = compiled_group.invocations[0]
    source_refs = tuple(spec.ref() for spec in invocation.contract.artifact_inputs)
    assert source_refs == (source_spec.ref(),)
    assert tuple(
        binding.alias
        for binding in source_binding_plan.for_artifact_refs(
            source_refs
        ).binding_declarations
    ) == ("OrigBlue",)
    assert tuple(
        binding.alias for binding in source_binding_plan.binding_declarations
    ) == ("OrigBlue", "OrigGreen")


def test_compiled_implicit_main_flow_uses_execution_component_source_anchor() -> None:
    source = ArtifactSpec.input("OrigBlue", ImageArtifactType)
    runtime_image = ArtifactSpec.input(
        "RGBImage",
        ImageArtifactType,
        parameter_name="image_to_save",
    )
    output = ArtifactSpec.output(
        "SavedRGBImage",
        ImageArtifactType,
        relations=(GroupLineageSourceRelation(source=runtime_image.ref()),),
    )

    @artifact_inputs(source, runtime_image)
    @artifact_outputs(output)
    @special_inputs("image_to_save")
    def save_image(image, *, image_to_save: np.ndarray):
        del image_to_save
        return image

    runtime_plan = ArtifactInputPlan(
        name=runtime_image.name,
        path="/memory/RGBImage.pkl",
        artifact_type=runtime_image.artifact_type,
    )
    output_plan = ArtifactOutputPlan(
        name=output.name,
        path="/memory/SavedRGBImage.pkl",
        artifact_type=output.artifact_type,
        relations=output.relations,
    )
    compiled_pattern = compile_function_pattern(
        {"3": save_image},
        {plan.ref(): plan for plan in (runtime_plan,)},
        {plan.ref(): plan for plan in (output_plan,)},
    )
    compiled_pattern = PathPlannerArtifactStage(
        PathPlanner.__new__(PathPlanner)
    ).compile_invocation_input_edges(
        compiled_pattern,
        artifact_inputs={runtime_plan.ref(): runtime_plan},
        relation_source_scopes={
            runtime_image.ref(): runtime_plan.producer_group_scope(),
        },
        execution_group_scope=ComponentGroupScope.from_raw(
            ("3",),
            component=AllComponents.CHANNEL,
        ),
        consumer_variable_components=ComponentSet(),
    )
    invocation = next(compiled_pattern.iter_invocations())
    assert tuple(edge.spec for edge in invocation.artifact_input_edges) == (
        source,
        runtime_image,
    )
    assert tuple(
        edge.spec
        for edge in invocation.artifact_input_edges
        if edge.storage_plan is not None
    ) == (runtime_image,)
    assert invocation.artifact_output_plans == (output_plan,)
    source_binding_plan = CompiledSourceBindingPlan(
        bindings=(
            NamedSourceBinding(
                alias="OrigBlue",
                selector=SourceSelector(
                    components=(ComponentSelector(AllComponents.CHANNEL, "1"),),
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "1"),),
            ),
            NamedSourceBinding(
                alias="OrigRed",
                selector=SourceSelector(
                    components=(ComponentSelector(AllComponents.CHANNEL, "3"),),
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "3"),),
            ),
        ),
        match_plan=SourceBindingMatchPlan(method=SourceBindingMatchMethod.ORDER),
    )
    plan = SimpleNamespace(
        axis_id="A01",
        step_index=16,
        step_name="SaveImages",
        main_input_dependency=StepInputDependency.pipeline_start(),
        source_binding_plan=source_binding_plan,
        execution_group_scope=ComponentGroupScope.from_raw(
            ("3",),
            component=AllComponents.CHANNEL,
        ),
        compiled_function_pattern=compiled_pattern,
    )
    pattern_filter = _anchor_executor(
        plan=plan,
        parser=SourceSchemaFilenameParser(),
        output_manifest=StepOutputManifestStore(),
        source_workspace_projection_cache=VirtualWorkspaceSourceProjectionCache(),
    )
    grouped_patterns = {
        "1": ("A01_s001_w1_z001_t001.tif",),
        "3": ("A01_s001_w3_z001_t001.tif",),
    }

    source_anchors = pattern_filter.source_bound_anchor_patterns(grouped_patterns)
    assert source_anchors == {
        "1": (),
        "3": ("A01_s001_w3_z001_t001.tif",),
    }
    assert pattern_filter.execution_group_anchor_patterns(source_anchors) == {
        "3": ("A01_s001_w3_z001_t001.tif",),
    }


def test_source_anchored_dict_pattern_excludes_out_of_scope_source_group() -> None:
    source = ArtifactSpec.input("OrigBlue", ImageArtifactType)

    @artifact_inputs(source)
    def exact_source_input(image):
        return image

    compiled_pattern = compile_function_pattern(
        {"1": exact_source_input},
        {},
        {},
    )
    source_binding_plan = CompiledSourceBindingPlan(
        bindings=(
            NamedSourceBinding(
                alias="OrigBlue",
                selector=SourceSelector(
                    components=(ComponentSelector(AllComponents.CHANNEL, "1"),),
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "1"),),
            ),
        ),
        match_plan=SourceBindingMatchPlan(method=SourceBindingMatchMethod.ORDER),
    )
    plan = SimpleNamespace(
        axis_id="A01",
        step_index=0,
        step_name="ExactSourceInput",
        main_input_dependency=StepInputDependency.pipeline_start(),
        source_binding_plan=source_binding_plan,
        execution_group_scope=ComponentGroupScope.from_raw(
            ("1",),
            component=AllComponents.CHANNEL,
        ),
        compiled_function_pattern=compiled_pattern,
    )
    pattern_filter = _anchor_executor(
        plan=plan,
        parser=SourceSchemaFilenameParser(),
        output_manifest=StepOutputManifestStore(),
        source_workspace_projection_cache=VirtualWorkspaceSourceProjectionCache(),
    )
    grouped_patterns = {
        "1": ("A01_s001_w1_z001_t001.tif",),
        "2": ("A01_s001_w2_z001_t001.tif",),
    }

    source_anchors = pattern_filter.source_bound_anchor_patterns(grouped_patterns)

    assert source_anchors == {
        "1": ("A01_s001_w1_z001_t001.tif",),
        "2": (),
    }
    assert pattern_filter.execution_group_anchor_patterns(source_anchors) == {
        "1": ("A01_s001_w1_z001_t001.tif",),
    }


def test_exact_source_artifact_filters_undeclared_detected_component_groups() -> None:
    source = ArtifactSpec.input("OrigBlue", ImageArtifactType)

    @artifact_inputs(source)
    def exact_source_input(image):
        return image

    source_binding_plan = CompiledSourceBindingPlan(
        bindings=(
            NamedSourceBinding(
                alias="OrigBlue",
                selector=SourceSelector(
                    components=(ComponentSelector(AllComponents.CHANNEL, "1"),),
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "1"),),
            ),
        ),
        match_plan=SourceBindingMatchPlan(method=SourceBindingMatchMethod.ORDER),
    )
    plan = SimpleNamespace(
        axis_id="A01",
        step_index=0,
        step_name="ExactSourceInput",
        main_input_dependency=StepInputDependency.pipeline_start(),
        source_binding_plan=source_binding_plan,
        execution_group_scope=ComponentGroupScope.from_raw(
            ("1",),
            component=AllComponents.CHANNEL,
        ),
        compiled_function_pattern=compile_function_pattern(exact_source_input, {}, {}),
    )
    pattern_filter = _anchor_executor(
        plan=plan,
        parser=SourceSchemaFilenameParser(),
        output_manifest=StepOutputManifestStore(),
        source_workspace_projection_cache=VirtualWorkspaceSourceProjectionCache(),
    )

    filtered = pattern_filter.source_bound_anchor_patterns(
        {
            "1": ("A01_s001_w1_z001_t001.tif",),
            "2": ("A01_s001_w2_z001_t001.tif",),
            "3": ("A01_s001_w3_z001_t001.tif",),
        }
    )

    assert filtered == {
        "1": ("A01_s001_w1_z001_t001.tif",),
    }


def test_pipeline_start_anchors_project_raw_selectors_to_semantic_groups() -> None:
    bindings = (
        NamedSourceBinding(
            alias="MCP_DNA",
            selector=SourceSelector(
                components=(ComponentSelector(AllComponents.CHANNEL, "1"),),
            ),
            origin=SourceBindingOrigin.PIPELINE_START,
            component_identity=(ComponentSelector(AllComponents.CHANNEL, "MCP_DNA"),),
        ),
        NamedSourceBinding(
            alias="MCP_AGP",
            selector=SourceSelector(
                components=(ComponentSelector(AllComponents.CHANNEL, "2"),),
            ),
            origin=SourceBindingOrigin.PIPELINE_START,
            component_identity=(ComponentSelector(AllComponents.CHANNEL, "MCP_AGP"),),
        ),
    )
    plan = SimpleNamespace(
        axis_id="A01",
        main_input_dependency=StepInputDependency.pipeline_start(),
        source_binding_plan=CompiledSourceBindingPlan(bindings=bindings),
        execution_group_scope=ComponentGroupScope.from_raw(
            ("MCP_DNA", "MCP_AGP"),
            component=AllComponents.CHANNEL,
        ),
        compiled_function_pattern=compile_function_pattern(
            lambda image: image,
            {},
            {},
        ),
    )
    pattern_filter = _anchor_executor(
        plan=plan,
        parser=SourceSchemaFilenameParser(),
        output_manifest=StepOutputManifestStore(),
        source_workspace_projection_cache=VirtualWorkspaceSourceProjectionCache(),
    )

    filtered = pattern_filter.source_bound_anchor_patterns(
        {
            "1": ("A01_s001_w1_z001_t001.tif",),
            "2": ("A01_s001_w2_z001_t001.tif",),
        }
    )

    assert filtered == {
        "MCP_DNA": ("A01_s001_w1_z001_t001.tif",),
        "MCP_AGP": ("A01_s001_w2_z001_t001.tif",),
    }


@pytest.fixture
def preserve_global_pipeline_context():
    context = GlobalContextValues.capture(GlobalPipelineConfig)
    yield
    context.apply()


def test_first_step_prepares_raw_source_anchors_under_semantic_binding_groups(
    tmp_path: Path,
    preserve_global_pipeline_context,
) -> None:
    from multiprocessing import SimpleQueue

    import tifffile
    from objectstate import ObjectStateRegistry
    from objectstate.lazy_factory import ensure_global_config_context

    from openhcs.constants import Microscope
    from openhcs.core.config import PipelineConfig
    from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
    from openhcs.core.progress import set_progress_queue
    from openhcs.core.source_bindings import LazyStepSourceBindingsConfig
    from openhcs.core.steps.function_runtime import (
        PatternGroupExecutionScope,
        PatternGroupExecutionRequest,
    )
    from openhcs.core.steps.function_step import FunctionStep

    image_dir = tmp_path / "TimePoint_1"
    image_dir.mkdir()
    (tmp_path / "plate.HTD").write_text(
        "\n".join(('"XSites", 1', '"YSites", 1', '"PixelSizeUM", 1.0')),
        encoding="utf-8",
    )
    for channel in (1, 2):
        tifffile.imwrite(
            image_dir / f"A01_s001_w{channel}_z001_t001.tif",
            np.ones((8, 8), dtype=np.uint16),
        )
    bindings = (
        NamedSourceBinding(
            alias="MCP_DNA",
            selector=SourceSelector(
                components=(ComponentSelector(AllComponents.CHANNEL, "1"),),
            ),
            component_identity=(ComponentSelector(AllComponents.CHANNEL, "MCP_DNA"),),
        ),
        NamedSourceBinding(
            alias="MCP_AGP",
            selector=SourceSelector(
                components=(ComponentSelector(AllComponents.CHANNEL, "2"),),
            ),
            component_identity=(ComponentSelector(AllComponents.CHANNEL, "MCP_AGP"),),
        ),
    )
    pipeline_config = PipelineConfig(
        step_source_bindings_config=LazyStepSourceBindingsConfig(bindings=bindings),
    )
    global_config = GlobalPipelineConfig(
        microscope=Microscope.IMAGEXPRESS,
        num_workers=1,
    )

    ObjectStateRegistry.clear()
    set_progress_queue(SimpleQueue())
    try:
        ensure_global_config_context(GlobalPipelineConfig, global_config)
        compilation = (
            PipelineOrchestrator(
                tmp_path,
                pipeline_config=pipeline_config,
            )
            .initialize()
            .compile_pipelines(
                pipeline_definition=[FunctionStep(func=_identity_source_image)],
                well_filter=["A01"],
                is_zmq_execution=True,
            )
        )
    finally:
        set_progress_queue(None)

    context = compilation.runtime_contexts["A01"]
    executor = FunctionStepExecutor(context, 0)
    grouped_patterns = executor._prepare_groups(executor._detect_patterns())

    assert executor.plan.main_input_dependency == StepInputDependency.pipeline_start()
    assert executor.plan.source_binding_plan.has_primary_content
    assert grouped_patterns == {
        "MCP_DNA": ("A01_s{iii}_w1_z001_t001.tif",),
        "MCP_AGP": ("A01_s{iii}_w2_z001_t001.tif",),
    }

    request = PatternGroupExecutionRequest(
        context=context,
        execution_plan=executor.plan,
        compiled_group=executor.plan.compiled_function_pattern.default_group,
        component_value="MCP_DNA",
        pattern_group_info=grouped_patterns["MCP_DNA"][0],
        component_index=0,
        component_count=2,
    )
    loaded = request.load_input_stack()

    assert loaded[0] == ["A01_s001_w1_z001_t001.tif"]
    assert context.filemanager.exists(
        str(executor.plan.input_dir / "A01_s001_w1_z001_t001.tif"),
        Backend.MEMORY.value,
    )
    assert not context.filemanager.exists(
        str(executor.plan.input_dir / "A01_s001_w2_z001_t001.tif"),
        Backend.MEMORY.value,
    )


def test_source_bound_artifact_managed_step_keeps_source_anchors() -> None:
    output = ArtifactSpec.output("IllumStain1", ImageArtifactType)

    @artifact_outputs(output)
    @runtime_adapter("runtime", lambda _request: object())
    def source_bound_module(image, *, runtime):
        return image

    source_binding_plan = CompiledSourceBindingPlan(
        bindings=(
            NamedSourceBinding(
                alias="OrigStain1",
                selector=SourceSelector(
                    components=(ComponentSelector(AllComponents.CHANNEL, "1"),),
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "1"),),
            ),
        ),
        match_plan=SourceBindingMatchPlan(method=SourceBindingMatchMethod.ORDER),
    )
    compiled_pattern = compile_function_pattern(
        source_bound_module,
        {},
        {
            plan.ref(): plan
            for plan in (
                ArtifactOutputPlan(
                    name=output.name,
                    path="/memory/IllumStain1.pkl",
                    artifact_type=output.artifact_type,
                ),
            )
        },
    )
    plan = SimpleNamespace(
        axis_id="A01",
        main_input_dependency=StepInputDependency.pipeline_start(),
        source_binding_plan=source_binding_plan,
        execution_group_value=None,
        execution_group_scope=ComponentGroupScope.ungrouped(),
        compiled_function_pattern=compiled_pattern,
    )
    pattern_filter = _anchor_executor(
        plan=plan,
        parser=SourceSchemaFilenameParser(),
        output_manifest=StepOutputManifestStore(),
        source_workspace_projection_cache=VirtualWorkspaceSourceProjectionCache(),
    )
    grouped_patterns = {
        None: (
            "A01_s001_w1_z001_t001.tif",
            "A01_s002_w1_z001_t001.tif",
        )
    }

    assert pattern_filter._filter_anchor_patterns(grouped_patterns) == grouped_patterns


def test_default_callable_runtime_scope_projects_bindings_to_selected_group() -> None:
    from openhcs.core.steps.function_runtime import PatternGroupExecutionScope

    source_binding_plan = CompiledSourceBindingPlan(
        bindings=(
            NamedSourceBinding(
                alias="OrigStain1",
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "1"),),
            ),
            NamedSourceBinding(
                alias="OrigStain2",
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "2"),),
            ),
        )
    )
    scope = PatternGroupExecutionScope(
        context=SimpleNamespace(),
        execution_plan=SimpleNamespace(
            axis_id="A01",
            execution_group_scope=ComponentGroupScope.dynamic(AllComponents.CHANNEL),
            source_binding_plan=source_binding_plan,
            compiled_function_pattern=compile_function_pattern(
                lambda image: image,
                {},
                {},
            ),
        ),
        compiled_group=compile_function_pattern(
            lambda image: image,
            {},
            {},
        ).default_group,
        component_value="1",
    )

    assert tuple(
        binding.alias for binding in scope.source_binding_plan.binding_declarations
    ) == ("OrigStain1",)


def test_dict_callable_runtime_scope_projects_bindings_to_selected_group() -> None:
    from openhcs.core.steps.function_runtime import PatternGroupExecutionScope

    source_binding_plan = CompiledSourceBindingPlan(
        bindings=(
            NamedSourceBinding(
                alias="OrigStain1",
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "1"),),
            ),
            NamedSourceBinding(
                alias="OrigStain2",
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "2"),),
            ),
        )
    )
    compiled_pattern = compile_function_pattern(
        {"1": lambda image: image},
        {},
        {},
    )
    scope = PatternGroupExecutionScope(
        context=SimpleNamespace(),
        execution_plan=SimpleNamespace(
            axis_id="A01",
            execution_group_scope=ComponentGroupScope.dynamic(AllComponents.CHANNEL),
            source_binding_plan=source_binding_plan,
            compiled_function_pattern=compiled_pattern,
        ),
        compiled_group=compiled_pattern.require_group("1"),
        component_value="1",
    )

    assert tuple(
        binding.alias for binding in scope.source_binding_plan.binding_declarations
    ) == ("OrigStain1",)


def test_grouped_runtime_adapter_receives_component_selected_source_bindings() -> None:
    from openhcs.core.runtime_adapters import (
        RuntimePlaneProjection,
    )
    from openhcs.core.source_load_plan import SourceLoadPlan
    from openhcs.core.steps.function_runtime import (
        PatternGroupData,
        FunctionCoreExecutor,
    )

    source_binding_plan = CompiledSourceBindingPlan(
        bindings=(
            NamedSourceBinding(
                alias="OrigStain1",
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "1"),),
            ),
            NamedSourceBinding(
                alias="OrigStain2",
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "2"),),
            ),
        )
    )
    compiled_pattern = compile_function_pattern(
        lambda image: image,
        {},
        {},
    )
    execution_plan = CompiledStepPlan(
        step_index=0,
        step_name="consume channel source",
        step_type="FunctionStep",
        axis_id="A01",
        execution_group_scope=ComponentGroupScope.dynamic(AllComponents.CHANNEL),
        source_binding_plan=source_binding_plan,
        compiled_function_pattern=compiled_pattern,
        variable_components=(VariableComponents.SITE,),
        source_load_plan=SourceLoadPlan(),
    )
    scope = PatternGroupData(
        matching_files=["first.tif", "second.tif"],
        main_data_stack=np.zeros((2, 3, 4), dtype=np.uint16),
        context=SimpleNamespace(),
        execution_plan=execution_plan,
        compiled_group=compiled_pattern.default_group,
        component_value="1",
        artifact_inputs={},
        artifact_outputs={},
        runtime_plane_index=0,
        runtime_plane_count=2,
    )

    executor = FunctionCoreExecutor(
        group_data=scope,
        invocation=compiled_pattern.default_group.invocations[0],
        artifact_inputs={},
        artifact_outputs={},
        group_key="1",
        plane_projection=RuntimePlaneProjection.stack(),
        main_data_arg=scope.main_data_stack,
        source_memory_type="numpy",
    )
    request = executor.runtime_adapter_request(scope.main_data_stack)

    assert tuple(
        binding.alias for binding in scope.source_binding_plan.binding_declarations
    ) == ("OrigStain1",)
    assert tuple(
        binding.alias for binding in request.source_binding_plan.binding_declarations
    ) == ("OrigStain1",)

    from openhcs.interop.cellprofiler.runtime.module_execution import (
        cellprofiler_runtime_adapter_factory,
    )

    adapter = cellprofiler_runtime_adapter_factory(request)
    assert adapter.request is request
    assert not hasattr(adapter, "artifact_inputs")


def test_runtime_invocation_uses_only_active_source_bound_main_flow_edges(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from openhcs.core.artifacts import NoMainFlowOutput
    from openhcs.core.source_load_plan import SourceLoadPlan
    from openhcs.core.steps import function_runtime
    from openhcs.core.steps.function_runtime import (
        PatternGroupData,
    )

    source_binding_plan = CompiledSourceBindingPlan(
        bindings=tuple(
            NamedSourceBinding(alias=alias) for alias in ("OrigStain1", "OrigStain2")
        )
    )
    source_specs = tuple(
        binding.input_spec() for binding in source_binding_plan.binding_declarations
    )
    output_specs = tuple(
        ArtifactSpec.output(
            f"IllumStain{channel}",
            ImageArtifactType,
            relations=(GroupLineageSourceRelation(source=source.ref()),),
        )
        for channel, source in enumerate(source_specs, start=1)
    )
    output_plans = {
        spec.ref(): ArtifactOutputPlan(
            name=spec.name,
            path=f"/memory/{spec.name}.pkl",
            artifact_type=spec.artifact_type,
            group_keys=(channel,),
            group_component=AllComponents.CHANNEL,
            paths_by_group={channel: f"/memory/{spec.name}__{channel}.pkl"},
            relations=spec.relations,
        )
        for channel, spec in zip(("1", "2"), output_specs, strict=True)
    }

    @artifact_inputs(*source_specs)
    @artifact_outputs(*output_specs)
    def consume_channel_source(image):
        return image

    compiled_pattern = compile_function_pattern(
        consume_channel_source,
        {},
        output_plans,
    )
    invocation = compiled_pattern.default_group.invocations[0]
    invocation = invocation.with_artifact_input_edges(
        tuple(
            InvocationArtifactInputEdgePlan(
                key=edge_key,
                spec=spec,
                storage_plan=None,
                projection=None,
                main_flow_projection=MainFlowInputProjection.DECLARED_SOURCE_IMAGE,
            )
            for edge_key, spec in zip(
                InvocationArtifactInputProjectionKey.for_input_count(
                    invocation.key,
                    len(source_specs),
                ),
                source_specs,
                strict=True,
            )
        )
    )
    compiled_group = replace(
        compiled_pattern.default_group,
        invocations=(invocation,),
    )
    execution_plan = CompiledStepPlan(
        step_index=0,
        step_name="consume channel source",
        step_type="FunctionStep",
        axis_id="A01",
        execution_group_scope=ComponentGroupScope.dynamic(AllComponents.CHANNEL),
        source_binding_plan=source_binding_plan,
        input_memory_type="numpy",
        variable_components=(VariableComponents.SITE,),
        source_load_plan=SourceLoadPlan(),
        compiled_function_pattern=compiled_pattern,
        artifact_inputs={},
        artifact_outputs=output_plans,
    )
    scope = PatternGroupData(
        matching_files=["input.tif"],
        main_data_stack=np.zeros((1, 3, 4), dtype=np.uint16),
        context=SimpleNamespace(),
        execution_plan=execution_plan,
        compiled_group=compiled_group,
        component_value="1",
        artifact_inputs=dict(execution_plan.artifact_inputs),
        artifact_outputs=PatternGroupExecutionScope._select_output_plans_for_component(
            execution_plan.artifact_outputs, execution_plan.execution_group_scope, "1"
        ),
        runtime_plane_index=0,
        runtime_plane_count=1,
    )
    captured_executor_kwargs = []
    core_executor_type = function_runtime.FunctionCoreExecutor

    class CapturingExecutor(FunctionCoreExecutor):
        def __init__(self, **kwargs):
            captured_executor_kwargs.append(kwargs)
            super().__init__(**kwargs)

        def execute(self, *, debug_sink=None):
            return NoMainFlowOutput()

    monkeypatch.setattr(function_runtime, "FunctionCoreExecutor", CapturingExecutor)
    monkeypatch.setattr(
        function_runtime,
        "debug_event_sink_from_context",
        lambda context: SimpleNamespace(captures_invocation_events=lambda: False),
    )

    active_payload = ImagePayloadMetadata(
        source_image_names=("OrigStain1",),
    ).payload_with(np.zeros((1, 3, 4), dtype=np.uint16))
    scope = replace(scope, main_data_stack=active_payload)
    result = scope.execute_chain()

    assert isinstance(result, NoMainFlowOutput)
    assert tuple(
        edge.spec.name
        for edge in captured_executor_kwargs[0]["invocation"].artifact_input_edges
    ) == ("OrigStain1", "OrigStain2")
    assert tuple(
        edge.spec.name
        for edge in captured_executor_kwargs[0]["artifact_inputs"].values()
    ) == ("OrigStain1",)
    assert tuple(captured_executor_kwargs[0]["artifact_outputs"]) == (
        output_specs[0].ref(),
    )

    request = core_executor_type(**captured_executor_kwargs[0]).runtime_adapter_request(
        np.zeros((1, 3, 4), dtype=np.uint16)
    )

    assert tuple(edge.spec.name for edge in request.artifact_inputs.values()) == (
        "OrigStain1",
    )
    assert request.selected_artifact_input_specs().names() == ("OrigStain1",)


def test_source_roster_selection_cannot_replace_missing_stored_primary_epoch() -> None:
    from openhcs.core.artifacts import ArtifactInputProjectionPlan
    from openhcs.core.steps.function_runtime import (
        PatternGroupExecutionScope,
        FunctionCoreExecutor,
        PatternGroupData,
    )

    bindings = CompiledSourceBindingPlan(
        bindings=(NamedSourceBinding(alias="Original"),)
    )
    (source_spec,) = tuple(
        binding.input_spec() for binding in bindings.binding_declarations
    )

    @runtime_adapter("runtime", lambda _request: object(), manages_artifact_inputs=True)
    @artifact_inputs(source_spec)
    def consume_original(image, *, runtime):
        return image

    storage = ArtifactInputPlan(
        name=source_spec.name,
        artifact_type=source_spec.artifact_type,
        path="/memory/Original.pkl",
        source_step_id=0,
    )
    invocation = compile_function_pattern(
        consume_original, {storage.ref(): storage}, {}
    ).default_group.invocations[0]
    (key,) = InvocationArtifactInputProjectionKey.for_input_count(invocation.key, 1)
    invocation = invocation.with_artifact_input_edges(
        (
            InvocationArtifactInputEdgePlan(
                key=key,
                spec=source_spec,
                storage_plan=storage,
                projection=ArtifactInputProjectionPlan(
                    invocation_scope=ComponentGroupScope.ungrouped(),
                    producer_selection_scope=storage.producer_group_scope(),
                ),
                main_flow_projection=MainFlowInputProjection.COMPLETE_PAYLOAD,
            ),
        )
    )
    payload = ImagePayloadMetadata(source_image_names=("Other",)).payload_with(
        np.zeros((1, 2, 3))
    )
    loaded = PatternGroupData(
        context=SimpleNamespace(),
        execution_plan=CompiledStepPlan(
            step_index=0,
            step_name="Stored",
            step_type="FunctionStep",
            axis_id="A01",
            source_binding_plan=bindings,
        ),
        compiled_group=compile_function_pattern(
            consume_original, {storage.ref(): storage}, {}
        ).default_group,
        artifact_inputs={storage.ref(): storage},
        artifact_outputs={},
        runtime_plane_index=0,
        runtime_plane_count=1,
        matching_files=["source.tif"],
        main_data_stack=payload,
    )
    with pytest.raises(
        ValueError, match="producer cannot substitute.*current payload epoch"
    ):
        FunctionCoreExecutor.from_group_invocation(
            loaded,
            invocation,
            main_data_arg=payload,
            source_memory_type="numpy",
            declared_source_bindings=loaded.execution_plan.source_binding_plan,
        )


def test_runtime_chain_skips_adapter_invocation_without_component_outputs(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from openhcs.core.function_patterns import CompiledFunctionGroup
    from openhcs.core.source_load_plan import SourceLoadPlan
    from openhcs.core.steps import function_runtime
    from openhcs.core.steps.function_runtime import (
        PatternGroupData,
    )

    first_spec = ArtifactSpec.output("FirstLabels", ObjectLabelsArtifactType)
    second_spec = ArtifactSpec.output("SecondLabels", ObjectLabelsArtifactType)
    first_plan = ArtifactOutputPlan(
        name=first_spec.name,
        path="/memory/FirstLabels.pkl",
        artifact_type=first_spec.artifact_type,
        group_keys=("1",),
        group_component=AllComponents.CHANNEL,
        paths_by_group={"1": "/memory/FirstLabels_1.pkl"},
    )
    second_plan = ArtifactOutputPlan(
        name=second_spec.name,
        path="/memory/SecondLabels.pkl",
        artifact_type=second_spec.artifact_type,
        group_keys=("2",),
        group_component=AllComponents.CHANNEL,
        paths_by_group={"2": "/memory/SecondLabels_2.pkl"},
    )

    @runtime_adapter(
        "runtime",
        lambda _request: object(),
        artifact_output_policy=AdapterRecordedArtifactOutputPolicy,
    )
    @artifact_outputs(first_spec)
    def record_first_labels(image, *, runtime):
        del runtime
        return image

    @runtime_adapter(
        "runtime",
        lambda _request: object(),
        artifact_output_policy=AdapterRecordedArtifactOutputPolicy,
    )
    @artifact_outputs(second_spec)
    def record_second_labels(image, *, runtime):
        del runtime
        return image

    first_invocation = next(
        compile_function_pattern(
            record_first_labels,
            {},
            {first_plan.ref(): first_plan},
        ).iter_invocations()
    )
    second_invocation = next(
        compile_function_pattern(
            record_second_labels,
            {},
            {second_plan.ref(): second_plan},
        ).iter_invocations()
    )
    compiled_group = CompiledFunctionGroup(
        group_key="default",
        invocations=(first_invocation, second_invocation),
    )
    output_plans = {
        first_plan.ref(): first_plan,
        second_plan.ref(): second_plan,
    }
    execution_plan = CompiledStepPlan(
        axis_id="A01",
        step_index=0,
        step_scope_id="pipeline::step_0",
        step_name="record labels",
        step_type="FunctionStep",
        execution_group_scope=ComponentGroupScope.dynamic(AllComponents.CHANNEL),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
        source_load_plan=SourceLoadPlan(),
        input_memory_type="numpy",
        variable_components=(VariableComponents.SITE,),
        artifact_inputs={},
        artifact_outputs=output_plans,
    )
    scope = PatternGroupData(
        matching_files=["input.tif"],
        main_data_stack=np.zeros((1, 3, 4), dtype=np.uint16),
        context=SimpleNamespace(),
        execution_plan=execution_plan,
        compiled_group=compiled_group,
        component_value="1",
        artifact_inputs=dict(execution_plan.artifact_inputs),
        artifact_outputs=PatternGroupExecutionScope._select_output_plans_for_component(
            execution_plan.artifact_outputs, execution_plan.execution_group_scope, "1"
        ),
        runtime_plane_index=0,
        runtime_plane_count=1,
    )
    executed = []

    class CapturingExecutor(FunctionCoreExecutor):
        def __init__(self, **kwargs):
            super().__init__(**kwargs)

        def execute(self, *, debug_sink=None):
            del debug_sink
            executed.append(self.invocation.key.function_name)
            return np.zeros((1, 3, 4), dtype=np.uint16)

        def memory_types(self):
            return SimpleNamespace(output_type="numpy")

    monkeypatch.setattr(function_runtime, "FunctionCoreExecutor", CapturingExecutor)
    monkeypatch.setattr(
        function_runtime,
        "debug_event_sink_from_context",
        lambda context: SimpleNamespace(captures_invocation_events=lambda: False),
    )

    scope.execute_chain()

    assert executed == ["record_first_labels"]


def test_invocation_source_artifact_owns_cross_component_runtime_binding_scope() -> (
    None
):
    from openhcs.core.steps.function_runtime import PatternGroupExecutionScope

    source_binding_plan = CompiledSourceBindingPlan(
        bindings=(
            NamedSourceBinding(
                alias="OrigStain1",
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "1"),),
            ),
            NamedSourceBinding(
                alias="OrigStain2",
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "2"),),
            ),
        )
    )
    source_spec = source_binding_plan.binding_declarations[0].input_spec()

    @artifact_inputs(source_spec)
    def exact_source_input(image):
        return image

    compiled_pattern = compile_function_pattern(exact_source_input, {}, {})
    scope = PatternGroupExecutionScope(
        context=SimpleNamespace(),
        execution_plan=SimpleNamespace(
            axis_id="A01",
            execution_group_scope=ComponentGroupScope.dynamic(AllComponents.SITE),
            source_binding_plan=source_binding_plan,
            compiled_function_pattern=compiled_pattern,
        ),
        compiled_group=compiled_pattern.default_group,
        component_value="1",
    )

    assert tuple(
        binding.alias for binding in scope.source_binding_plan.binding_declarations
    ) == ("OrigStain1",)


def test_main_flow_input_owns_runtime_binding_scope_with_auxiliary_source() -> None:
    from openhcs.core.steps.function_runtime import PatternGroupExecutionScope

    source_binding_plan = CompiledSourceBindingPlan(
        bindings=(
            NamedSourceBinding(
                alias="OrigStain1",
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "1"),),
            ),
            NamedSourceBinding(
                alias="OrigStain2",
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "2"),),
            ),
        )
    )
    source_spec = source_binding_plan.binding_declarations[0].input_spec()
    main_flow_spec = source_binding_plan.binding_declarations[1].input_spec()

    @artifact_inputs(main_flow_spec, source_spec)
    def main_flow_with_auxiliary_source(image):
        return image

    compiled_pattern = compile_function_pattern(
        main_flow_with_auxiliary_source,
        {},
        {},
    )
    invocation = compiled_pattern.default_group.invocations[0]
    invocation = invocation.with_artifact_input_edges(
        tuple(
            InvocationArtifactInputEdgePlan(
                key=edge_key,
                spec=spec,
                storage_plan=None,
                projection=None,
                main_flow_projection=(MainFlowInputProjection.DECLARED_SOURCE_IMAGE if input_index == 0 else None),
            )
            for input_index, (edge_key, spec) in enumerate(
                zip(
                    InvocationArtifactInputProjectionKey.for_input_count(
                        invocation.key,
                        2,
                    ),
                    (main_flow_spec, source_spec),
                    strict=True,
                )
            )
        )
    )
    compiled_pattern = replace(
        compiled_pattern,
        groups=(
            replace(
                compiled_pattern.default_group,
                invocations=(invocation,),
            ),
        ),
    )
    scope = PatternGroupExecutionScope(
        context=SimpleNamespace(),
        execution_plan=SimpleNamespace(
            axis_id="A01",
            execution_group_scope=ComponentGroupScope.dynamic(AllComponents.CHANNEL),
            source_binding_plan=source_binding_plan,
            compiled_function_pattern=compiled_pattern,
        ),
        compiled_group=compiled_pattern.default_group,
        component_value="2",
    )

    assert tuple(
        binding.alias for binding in scope.source_binding_plan.binding_declarations
    ) == ("OrigStain1", "OrigStain2")
    assert tuple(
        binding.alias
        for binding in scope.main_flow_source_binding_plan.binding_declarations
    ) == ("OrigStain2",)


def test_payload_provenance_excludes_auxiliary_binding_from_main_flow_scope() -> None:
    from openhcs.core.steps.function_runtime import PatternGroupExecutionScope

    source_binding_plan = CompiledSourceBindingPlan(
        bindings=(
            NamedSourceBinding(
                alias="FilenamePrefix",
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "1"),),
            ),
        )
    )
    source_spec = source_binding_plan.binding_declarations[0].input_spec()

    @artifact_inputs(source_spec)
    def save_main_flow_with_source_prefix(image):
        return image

    compiled_pattern = compile_function_pattern(
        save_main_flow_with_source_prefix,
        {},
        {},
    )
    scope = PatternGroupExecutionScope(
        context=SimpleNamespace(),
        execution_plan=SimpleNamespace(
            axis_id="A01",
            execution_group_scope=ComponentGroupScope.dynamic(AllComponents.CHANNEL),
            source_binding_plan=source_binding_plan,
            variable_components=(VariableComponents.SITE,),
            compiled_function_pattern=compiled_pattern,
        ),
        compiled_group=compiled_pattern.default_group,
        component_value="2",
    )
    payload = ImagePayloadMetadata(
        source_image_names=("MainFlowChannel",),
    ).payload_with(np.zeros((1, 3, 4), dtype=np.uint16))

    assert not scope.active_main_flow_source_binding_plan(payload).binding_declarations
    assert tuple(
        binding.alias for binding in scope.source_binding_plan.binding_declarations
    ) == ("FilenamePrefix",)


def test_payload_provenance_outranks_unrelated_artifact_execution_group() -> None:
    from openhcs.core.steps.function_runtime import PatternGroupExecutionScope

    source_binding_plan = CompiledSourceBindingPlan(
        bindings=(
            NamedSourceBinding(
                alias="OrigGreen",
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "2"),),
            ),
        )
    )
    compiled_pattern = compile_function_pattern(lambda image: image, {}, {})
    scope = PatternGroupExecutionScope(
        context=SimpleNamespace(),
        execution_plan=SimpleNamespace(
            axis_id="A01",
            execution_group_scope=ComponentGroupScope.from_raw(
                ("1",),
                component=AllComponents.CHANNEL,
            ),
            source_binding_plan=source_binding_plan,
            variable_components=(VariableComponents.SITE,),
        ),
        compiled_group=compiled_pattern.default_group,
        component_value="1",
    )
    payload = ImagePayloadMetadata(
        source_image_names=("OrigGreen",),
    ).payload_with(np.zeros((1, 3, 4), dtype=np.uint16))

    assert tuple(
        binding.alias
        for binding in scope.active_main_flow_source_binding_plan(
            payload
        ).binding_declarations
    ) == ("OrigGreen",)


def test_payload_provenance_preserves_bindings_across_a_variable_stack_axis() -> None:
    from openhcs.core.steps.function_runtime import PatternGroupExecutionScope

    source_binding_plan = CompiledSourceBindingPlan(
        bindings=tuple(
            NamedSourceBinding(
                alias=alias,
                component_identity=(ComponentSelector(AllComponents.CHANNEL, channel),),
            )
            for alias, channel in (("OrigBlue", "1"), ("OrigGreen", "2"))
        )
    )
    source_specs = tuple(
        binding.input_spec() for binding in source_binding_plan.binding_declarations
    )

    @artifact_inputs(*source_specs)
    def consume_channel_stack(image):
        return image

    compiled_pattern = compile_function_pattern(
        consume_channel_stack,
        {},
        {},
    )
    invocation = compiled_pattern.default_group.invocations[0]
    invocation = invocation.with_artifact_input_edges(
        tuple(
            InvocationArtifactInputEdgePlan(
                key=edge_key,
                spec=spec,
                storage_plan=None,
                projection=None,
                main_flow_projection=MainFlowInputProjection.DECLARED_SOURCE_IMAGE,
            )
            for edge_key, spec in zip(
                InvocationArtifactInputProjectionKey.for_input_count(
                    invocation.key,
                    len(source_specs),
                ),
                source_specs,
                strict=True,
            )
        )
    )
    compiled_group = replace(
        compiled_pattern.default_group,
        invocations=(invocation,),
    )
    scope = PatternGroupExecutionScope(
        context=SimpleNamespace(),
        execution_plan=SimpleNamespace(
            axis_id="A01",
            execution_group_scope=ComponentGroupScope.dynamic(AllComponents.SITE),
            source_binding_plan=source_binding_plan,
            variable_components=(VariableComponents.CHANNEL,),
        ),
        compiled_group=compiled_group,
        component_value="1",
    )
    payload = ImagePayloadMetadata(
        source_image_names=("OrigBlue",),
    ).payload_with(np.zeros((2, 3, 4), dtype=np.uint16))

    assert tuple(
        binding.alias
        for binding in scope.active_main_flow_source_binding_plan(
            payload
        ).binding_declarations
    ) == ("OrigBlue", "OrigGreen")


def test_main_flow_source_scope_intersects_cross_component_invocation_inputs() -> None:
    from openhcs.core.steps.function_runtime import PatternGroupExecutionScope

    source_binding_plan = CompiledSourceBindingPlan(
        bindings=tuple(
            NamedSourceBinding(
                alias=alias,
                component_identity=(ComponentSelector(AllComponents.CHANNEL, channel),),
            )
            for alias, channel in (
                ("Worms", "1"),
                ("GFP", "2"),
                ("mCherry", "3"),
            )
        )
    )
    selected_specs = tuple(
        binding.input_spec() for binding in source_binding_plan.binding_declarations[1:]
    )

    @artifact_inputs(*selected_specs)
    def consume_selected_channels(image):
        return image

    compiled_pattern = compile_function_pattern(consume_selected_channels, {}, {})
    invocation = compiled_pattern.default_group.invocations[0]
    invocation = invocation.with_artifact_input_edges(
        tuple(
            InvocationArtifactInputEdgePlan(
                key=edge_key,
                spec=spec,
                storage_plan=None,
                projection=None,
                main_flow_projection=MainFlowInputProjection.DECLARED_SOURCE_IMAGE,
            )
            for edge_key, spec in zip(
                InvocationArtifactInputProjectionKey.for_input_count(
                    invocation.key,
                    len(selected_specs),
                ),
                selected_specs,
                strict=True,
            )
        )
    )
    compiled_pattern = replace(
        compiled_pattern,
        groups=(
            replace(
                compiled_pattern.default_group,
                invocations=(invocation,),
            ),
        ),
    )
    scope = PatternGroupExecutionScope(
        context=SimpleNamespace(),
        execution_plan=SimpleNamespace(
            axis_id="A01",
            execution_group_scope=ComponentGroupScope.dynamic(AllComponents.SITE),
            source_binding_plan=source_binding_plan,
            compiled_function_pattern=compiled_pattern,
        ),
        compiled_group=compiled_pattern.default_group,
        component_value="1",
    )

    assert tuple(
        binding.alias
        for binding in scope.main_flow_source_binding_plan.binding_declarations
    ) == ("GFP", "mCherry")
    assert tuple(
        binding.alias for binding in scope.source_binding_plan.binding_declarations
    ) == ("GFP", "mCherry")


def test_special_input_preserves_ordered_declared_main_flow_sources() -> None:
    from openhcs.core.steps.function_runtime import PatternGroupExecutionScope

    source_binding_plan = CompiledSourceBindingPlan(
        bindings=tuple(
            NamedSourceBinding(
                alias=alias,
                component_identity=(ComponentSelector(AllComponents.CHANNEL, channel),),
            )
            for alias, channel in (("SMI312", "4"), ("Hoechst", "1"))
        )
    )

    @artifact_inputs("pixel_size")
    def measure_neurites(image, pixel_size=1.0):
        del pixel_size
        return image

    compiled_pattern = compile_function_pattern(measure_neurites, {}, {})
    invocation = compiled_pattern.default_group.invocations[0]
    pixel_size_spec = invocation.contract.artifact_inputs[0]
    invocation = invocation.with_artifact_input_edges(
        (
            InvocationArtifactInputEdgePlan(
                key=InvocationArtifactInputProjectionKey.for_input_count(
                    invocation.key,
                    1,
                )[0],
                spec=pixel_size_spec,
                storage_plan=None,
                projection=None,

            ),
        )
    )
    compiled_pattern = replace(
        compiled_pattern,
        groups=(
            replace(
                compiled_pattern.default_group,
                invocations=(invocation,),
            ),
        ),
    )
    scope = PatternGroupExecutionScope(
        context=SimpleNamespace(),
        execution_plan=SimpleNamespace(
            axis_id="R04C09",
            execution_group_scope=ComponentGroupScope.dynamic(AllComponents.SITE),
            source_binding_plan=source_binding_plan,
            compiled_function_pattern=compiled_pattern,
        ),
        compiled_group=compiled_pattern.default_group,
        component_value="11",
    )

    assert tuple(
        binding.alias
        for binding in scope.main_flow_source_binding_plan.binding_declarations
    ) == ("SMI312", "Hoechst")


def test_pipeline_start_main_flow_survives_prior_producer_image_input(
    tmp_path: Path,
    preserve_global_pipeline_context,
) -> None:
    from multiprocessing import SimpleQueue

    import tifffile
    from objectstate import ObjectStateRegistry
    from objectstate.lazy_factory import ensure_global_config_context

    from openhcs.constants import Microscope
    from openhcs.constants.input_source import InputSource
    from openhcs.core.config import (
        LazyProcessingConfig,
        PipelineConfig,
    )
    from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
    from openhcs.core.progress import set_progress_queue
    from openhcs.core.source_bindings import (
        LazySourceBindingsConfig,
        LazyStepSourceBindingsConfig,
    )
    from openhcs.core.steps.function_runtime import PatternGroupExecutionScope
    from openhcs.core.steps.function_step import FunctionStep

    image_dir = tmp_path / "TimePoint_1"
    image_dir.mkdir()
    (tmp_path / "plate.HTD").write_text(
        "\n".join(('"XSites", 1', '"YSites", 1', '"PixelSizeUM", 1.0')),
        encoding="utf-8",
    )
    tifffile.imwrite(
        image_dir / "A01_s001_w1_z001_t001.tif",
        np.ones((8, 8), dtype=np.uint16),
    )
    primary_source = NamedSourceBinding(
        alias="Primary",
        component_identity=(ComponentSelector(AllComponents.CHANNEL, "1"),),
    )
    pipeline_start = LazyProcessingConfig(
        variable_components=[VariableComponents.SITE],
        group_by=GroupBy.CHANNEL,
        input_source=InputSource.PIPELINE_START,
    )
    steps = [
        FunctionStep(
            func=_produce_mask_for_main_flow_regression,
            name="produce_mask",
            processing_config=pipeline_start,
        ),
        FunctionStep(
            func=_consume_source_with_prior_mask,
            name="consume_source_with_prior_mask",
            processing_config=pipeline_start,
            source_bindings=LazyStepSourceBindingsConfig(enabled=True),
        ),
    ]
    pipeline_config = PipelineConfig(
        source_bindings_config=LazySourceBindingsConfig(
            bindings=(primary_source,),
        )
    )
    global_config = GlobalPipelineConfig(
        microscope=Microscope.IMAGEXPRESS,
        num_workers=1,
    )

    ObjectStateRegistry.clear()
    set_progress_queue(SimpleQueue())
    try:
        ensure_global_config_context(GlobalPipelineConfig, global_config)
        compilation = (
            PipelineOrchestrator(
                tmp_path,
                pipeline_config=pipeline_config,
            )
            .initialize()
            .compile_pipelines(
                pipeline_definition=steps,
                well_filter=["A01"],
                is_zmq_execution=True,
            )
        )
    finally:
        set_progress_queue(None)

    context = compilation.runtime_contexts["A01"]
    consumer_plan = context.step_plans[1]
    compiled_pattern = consumer_plan.compiled_function_pattern
    assert compiled_pattern is not None
    invocation = next(compiled_pattern.iter_invocations())
    (mask_edge,) = invocation.artifact_input_edges
    scope = PatternGroupExecutionScope(
        context=context,
        execution_plan=consumer_plan,
        compiled_group=compiled_pattern.default_group,
        component_value="1",
    )

    assert consumer_plan.main_input_dependency == StepInputDependency.pipeline_start()
    assert tuple(
        binding.alias
        for binding in consumer_plan.source_binding_plan.binding_declarations
    ) == ("Primary",)
    assert mask_edge.spec == _MAIN_FLOW_MASK_INPUT
    assert mask_edge.storage_plan is not None
    assert (mask_edge.main_flow_projection is not None) is False
    assert invocation.contract.accepts_implicit_main_flow_input is True
    assert compiled_pattern.default_group.main_flow_input_refs(source_bindings=CompiledSourceBindingPlan.empty()) is None
    assert tuple(
        binding.alias
        for binding in scope.main_flow_source_binding_plan.binding_declarations
    ) == ("Primary",)


def test_runtime_plane_count_comes_from_loaded_slices_not_dispatch_groups() -> None:
    from openhcs.core.steps.function_runtime import (
        PatternGroupData,
        PatternGroupExecutionRequest,
    )

    plan = SimpleNamespace(
        axis_id="A01",
        execution_group_scope=ComponentGroupScope.dynamic(AllComponents.CHANNEL),
        source_binding_plan=CompiledSourceBindingPlan(),
        artifact_inputs={},
        artifact_outputs={},
        variable_components=(VariableComponents.SITE,),
    )
    request = PatternGroupExecutionRequest(
        context=SimpleNamespace(),
        execution_plan=plan,
        compiled_group=compile_function_pattern(
            lambda image: image,
            {},
            {},
        ).default_group,
        component_value="1",
        pattern_group_info="A01_s{iii}_w1_z001_t001.tif",
        component_index=0,
        component_count=1,
    )
    scope = PatternGroupData.from_loaded_group(
        request,
        matching_files=[
            "A01_s001_w1_z001_t001.tif",
            "A01_s002_w1_z001_t001.tif",
        ],
        main_data_stack=ImagePayloadMetadata(
            source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
                paths=(
                    "A01_s001_w1_z003_t002.tif",
                    "A01_s002_w1_z003_t002.tif",
                ),
                component_metadata=(
                    {
                        "well": "A01",
                        "site": "1",
                        "channel": "1",
                        "z_index": "3",
                        "timepoint": "2",
                        "extension": ".tif",
                    },
                    {
                        "well": "A01",
                        "site": "2",
                        "channel": "1",
                        "z_index": "3",
                        "timepoint": "2",
                        "extension": ".tif",
                    },
                ),
            ),
        ).payload_with(np.zeros((2, 4, 5), dtype=np.float32)),
    )

    assert scope.runtime_plane_count == 2
    assert scope.axis_scope.fixed_component_values == (
        (AllComponents.Z_INDEX, "3"),
        (AllComponents.TIMEPOINT, "2"),
    )


def test_grouped_main_flow_context_uses_component_selected_output_plan() -> None:
    from openhcs.core.steps.function_runtime import (
        PatternGroupExecutionRequest,
    )

    corrected_stain_1_spec = ArtifactSpec.output(
        "CorrectedStain1",
        ImageArtifactType,
    )
    corrected_stain_2_spec = ArtifactSpec.output(
        "CorrectedStain2",
        ImageArtifactType,
    )
    corrected_stain_1 = ArtifactOutputPlan(
        name=corrected_stain_1_spec.name,
        path="/memory/CorrectedStain1.pkl",
        artifact_type=corrected_stain_1_spec.artifact_type,
        group_keys=("1",),
        group_component=AllComponents.CHANNEL,
        paths_by_group={"1": "/memory/CorrectedStain1_1.pkl"},
    )
    corrected_stain_2 = ArtifactOutputPlan(
        name=corrected_stain_2_spec.name,
        path="/memory/CorrectedStain2.pkl",
        artifact_type=corrected_stain_2_spec.artifact_type,
        group_keys=("2",),
        group_component=AllComponents.CHANNEL,
        paths_by_group={"2": "/memory/CorrectedStain2_2.pkl"},
    )
    plan = SimpleNamespace(
        artifact_inputs={},
        artifact_outputs={
            plan.ref(): plan for plan in (corrected_stain_1, corrected_stain_2)
        },
        execution_group_scope=ComponentGroupScope.dynamic(AllComponents.CHANNEL),
        source_binding_plan=CompiledSourceBindingPlan(),
    )

    @artifact_outputs(
        corrected_stain_1_spec,
        corrected_stain_2_spec,
    )
    def correct_illumination(image):
        return image

    compiled_group = compile_function_pattern(
        correct_illumination,
        {},
        {plan.ref(): plan for plan in (corrected_stain_1, corrected_stain_2)},
    ).default_group
    runtime = PatternGroupExecutionRequest(
        context=SimpleNamespace(),
        execution_plan=plan,
        compiled_group=compiled_group,
        component_value="1",
        pattern_group_info="A01_s{iii}_w1_z001_t001.tif",
        component_index=0,
        component_count=2,
    )

    context = runtime._unwrapped_main_flow_output_context()

    assert context is not None
    assert context.output_key == "CorrectedStain1"
    assert context.artifact_kind == ImageArtifactType.value


def test_adapter_recorded_outputs_use_compiled_canonical_context() -> None:
    from openhcs.core.steps.function_runtime import (
        PatternGroupExecutionRequest,
    )

    outline_spec = ArtifactSpec.output("outline", ImageArtifactType)
    first_labels_spec = ArtifactSpec.output("first_labels", ObjectLabelsArtifactType)
    second_labels_spec = ArtifactSpec.output("second_labels", ObjectLabelsArtifactType)
    output_plans = {
        spec.ref(): ArtifactOutputPlan(
            name=spec.name,
            path=f"/memory/{spec.name}.pkl",
            artifact_type=spec.artifact_type,
        )
        for spec in (outline_spec, first_labels_spec, second_labels_spec)
    }

    @runtime_adapter(
        "runtime",
        lambda _request: object(),
        artifact_output_policy=AdapterRecordedArtifactOutputPolicy,
    )
    @artifact_outputs(outline_spec, first_labels_spec, second_labels_spec)
    def record_mixed_outputs(image, *, runtime):
        del runtime
        return image

    compiled_group = compile_function_pattern(
        record_mixed_outputs,
        {},
        output_plans,
    ).default_group
    runtime = PatternGroupExecutionRequest(
        context=SimpleNamespace(),
        execution_plan=SimpleNamespace(
            artifact_inputs={},
            artifact_outputs=output_plans,
            execution_group_scope=ComponentGroupScope.ungrouped(),
            source_binding_plan=CompiledSourceBindingPlan.empty(),
        ),
        compiled_group=compiled_group,
        component_value="default",
        pattern_group_info="A01_s001_w1_z001_t001.tif",
        component_index=0,
        component_count=1,
    )

    context = runtime._unwrapped_main_flow_output_context()

    assert context is not None
    assert context.output_key == "outline"
    assert context.artifact_kind == ImageArtifactType.value


def test_component_output_selection_keeps_distinct_axes_with_equal_keys() -> None:
    from openhcs.core.steps.function_runtime import (
        PatternGroupExecutionScope,
        FunctionCoreExecutor,
        PatternGroupData,
    )

    channel_1 = ArtifactOutputPlan(
        name="Stain1",
        path="/memory/Stain1.pkl",
        artifact_type=ImageArtifactType,
        group_keys=("1",),
        group_component=AllComponents.CHANNEL,
        paths_by_group={"1": "/memory/Stain1_1.pkl"},
    )
    channel_2 = ArtifactOutputPlan(
        name="Stain2",
        path="/memory/Stain2.pkl",
        artifact_type=ImageArtifactType,
        group_keys=("2",),
        group_component=AllComponents.CHANNEL,
        paths_by_group={"2": "/memory/Stain2_2.pkl"},
    )
    plan = SimpleNamespace(
        artifact_inputs={},
        artifact_outputs={plan.ref(): plan for plan in (channel_1, channel_2)},
        execution_group_scope=ComponentGroupScope.dynamic(AllComponents.SITE),
    )

    selected = PatternGroupExecutionScope._select_output_plans_for_component(
        plan.artifact_outputs, plan.execution_group_scope, "1"
    )

    assert tuple(selected) == (channel_1.ref(), channel_2.ref())
    assert selected[channel_1.ref()].path == "/memory/Stain1_1.pkl"
    assert selected[channel_2.ref()].path == "/memory/Stain2_2.pkl"


def test_component_artifact_plans_reject_malformed_exact_plan_maps() -> None:
    from openhcs.core.steps.function_runtime import (
        PatternGroupExecutionScope,
        FunctionCoreExecutor,
        PatternGroupData,
    )

    input_plan = ArtifactInputPlan(
        name="InputImage",
        path="/memory/InputImage.pkl",
        artifact_type=ImageArtifactType,
    )
    output_plan = ArtifactOutputPlan(
        name="OutputImage",
        path="/memory/OutputImage.pkl",
        artifact_type=ImageArtifactType,
    )
    invalid_maps = (
        (
            {input_plan.name: input_plan},
            {},
            TypeError,
            "input maps require ArtifactSpecRef keys",
        ),
        (
            {input_plan.ref(): output_plan},
            {},
            TypeError,
            "input maps require ArtifactInputPlan values",
        ),
        (
            {ArtifactSpec.input("OtherInput", ImageArtifactType).ref(): (input_plan)},
            {},
            ValueError,
            "input key .* conflicts with plan ref",
        ),
        (
            {},
            {output_plan.name: output_plan},
            TypeError,
            "output maps require ArtifactSpecRef keys",
        ),
        (
            {},
            {output_plan.ref(): input_plan},
            TypeError,
            "output maps require ArtifactOutputPlan values",
        ),
        (
            {},
            {
                ArtifactSpec.output("OtherOutput", ImageArtifactType).ref(): (
                    output_plan
                )
            },
            ValueError,
            "output key .* conflicts with plan ref",
        ),
    )

    for invalid_inputs, invalid_outputs, error_type, message in invalid_maps:
        step_plan = SimpleNamespace(
            artifact_inputs=invalid_inputs,
            artifact_outputs=invalid_outputs,
            execution_group_scope=ComponentGroupScope.ungrouped(),
        )
        with pytest.raises(error_type, match=message):
            request = PatternGroupExecutionRequest(
                context=SimpleNamespace(),
                execution_plan=step_plan,
                compiled_group=compile_function_pattern(
                    lambda image: image, {}, {}
                ).default_group,
                pattern_group_info="fixture",
                component_index=0,
                component_count=1,
            )
            PatternGroupData.from_loaded_group(request, [], np.zeros((1, 2, 3)))


def test_grouped_runtime_scope_preserves_empty_source_binding_plan() -> None:
    from openhcs.core.steps.function_runtime import PatternGroupExecutionScope

    source_binding_plan = CompiledSourceBindingPlan.empty()
    compiled_pattern = compile_function_pattern(lambda image: image, {}, {})
    scope = PatternGroupExecutionScope(
        context=SimpleNamespace(),
        execution_plan=SimpleNamespace(
            axis_id="A01",
            execution_group_scope=ComponentGroupScope.dynamic(AllComponents.SITE),
            source_binding_plan=source_binding_plan,
        ),
        compiled_group=compiled_pattern.default_group,
        component_value="1",
    )

    assert scope.source_binding_plan is source_binding_plan


def test_grouped_runtime_source_expansion_uses_scoped_bindings(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from openhcs.core.steps import function_runtime

    source_binding_plan = CompiledSourceBindingPlan(
        bindings=(
            NamedSourceBinding(
                alias="OrigStain1",
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            SourceFilterSubject.FILE,
                            SourceFilterMatchType.CONTAINS,
                            "N_R",
                        ),
                    )
                ),
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "1"),),
            ),
            NamedSourceBinding(
                alias="OrigStain2",
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            SourceFilterSubject.FILE,
                            SourceFilterMatchType.CONTAINS,
                            "N_G",
                        ),
                    )
                ),
                component_identity=(ComponentSelector(AllComponents.CHANNEL, "2"),),
            ),
        )
    )
    compiled_pattern = compile_function_pattern(
        {"1": lambda image: image},
        {},
        {},
    )
    runtime = function_runtime.PatternGroupExecutionRequest(
        context=SimpleNamespace(
            source_image_set_identity_policy=SourceImageSetIdentityPolicy(
                frozenset((AllComponents.SITE,))
            )
        ),
        execution_plan=SimpleNamespace(
            axis_id="A01",
            execution_group_scope=ComponentGroupScope.dynamic(AllComponents.CHANNEL),
            main_input_dependency=StepInputDependency.pipeline_start(),
            source_binding_plan=source_binding_plan,
            compiled_function_pattern=compiled_pattern,
            variable_component_values=(VariableComponents.SITE.value,),
        ),
        compiled_group=compiled_pattern.require_group("1"),
        component_value="1",
        pattern_group_info="A01_s{iii}_w1_z001_t001.png",
        component_index=0,
        component_count=2,
    )
    captured_aliases: tuple[str, ...] = ()

    class MatchedImageSet:
        def expand(self, matching_files, *, source_universe):
            del source_universe
            return tuple(matching_files)

    def matched_image_set_from_plan(*, bindings, **_kwargs):
        nonlocal captured_aliases
        captured_aliases = tuple(binding.alias for binding in bindings)
        return MatchedImageSet()

    monkeypatch.setattr(
        function_runtime.SourceBindingMatchedImageSet,
        "from_plan",
        matched_image_set_from_plan,
    )
    monkeypatch.setattr(
        type(runtime),
        "_source_binding_candidate_context",
        lambda _request, *args, **kwargs: (lambda: SimpleNamespace())(*args, **kwargs),
    )
    monkeypatch.setattr(
        type(runtime),
        "_source_binding_load_universe",
        lambda _request, *args, **kwargs: (lambda: ())(*args, **kwargs),
    )

    matching_files = ["/input/A01_s001_N_R.png"]
    assert runtime._filter_matching_files_for_source_bindings(matching_files) == (
        matching_files
    )
    assert captured_aliases == ("OrigStain1",)


def test_alias_only_workspace_filter_excludes_unselected_source_and_orders_stack(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from openhcs.core.steps import function_runtime

    declarations = (
        NamedSourceBinding(alias="Hoechst"),
        NamedSourceBinding(alias="MAP2"),
        NamedSourceBinding(alias="SMI312"),
    )
    virtual_paths = tuple(
        f"R04C09_s011_w{channel}_z001_t001.tif" for channel in ("1", "2", "4")
    )
    source_planes = tuple(
        SourcePlaneProjection(
            address=OpenHCSPlaneAddress.from_values(
                well="R04C09",
                site="11",
                channel=channel,
                z_index="1",
                timepoint="1",
            ),
            ref=SourcePixelRef("disk", f"/source/ch{channel}.tiff"),
            source_alias=binding.alias,
        )
        for channel, binding in zip(("1", "2", "4"), declarations, strict=True)
    )
    projection = VirtualWorkspaceSourceProjection(
        source_refs_by_virtual_path={
            path: plane.ref
            for path, plane in zip(virtual_paths, source_planes, strict=True)
        },
        source_metadata_by_path={},
        source_projections_by_virtual_path={
            path: plane
            for path, plane in zip(virtual_paths, source_planes, strict=True)
        },
    )
    source_context = SourcePatternResolutionContext.from_projection(
        parser=SourceSchemaFilenameParser(),
        projection=projection,
    )
    selected_plan = CompiledSourceBindingPlan(
        bindings=(
            NamedSourceBinding(alias="SMI312"),
            NamedSourceBinding(alias="Hoechst"),
        )
    )
    runtime = PatternGroupExecutionRequest(
        context=SimpleNamespace(
            source_image_set_identity_policy=SourceImageSetIdentityPolicy()
        ),
        execution_plan=CompiledStepPlan(
            step_index=0,
            step_name="MetaXpress",
            step_type="FunctionStep",
            axis_id="A01",
            main_input_dependency=StepInputDependency.pipeline_start(),
            source_binding_plan=selected_plan,
        ),
        compiled_group=compile_function_pattern(
            lambda image: image, {}, {}
        ).default_group,
        pattern_group_info="fixture",
        component_index=0,
        component_count=1,
    )
    monkeypatch.setattr(
        type(runtime),
        "_source_binding_candidate_context",
        lambda _request, *args, **kwargs: (lambda: source_context)(*args, **kwargs),
    )
    monkeypatch.setattr(
        type(runtime),
        "_source_binding_load_universe",
        lambda _request, *args, **kwargs: (lambda: virtual_paths)(*args, **kwargs),
    )

    assert runtime._filter_matching_files_for_source_bindings(list(virtual_paths)) == [
        virtual_paths[2],
        virtual_paths[0],
    ]


def test_unbound_workspace_source_keeps_filename_component_provenance(
    tmp_path: Path,
) -> None:
    """Ordinary workspace sources retain fixed coordinates without bindings."""

    from openhcs.core.steps import function_runtime

    virtual_path = "A01_s002_w1_z003_t004.tif"
    full_virtual_path = str(tmp_path / virtual_path)
    source_ref = SourcePixelRef("disk", str(tmp_path / "raw-image.tif"))
    source_metadata = {
        SOURCE_BINDING_ALIAS_METADATA_FIELD: "OrigDNA",
        AllComponents.SITE.value: 2,
        AllComponents.CHANNEL.value: 1,
        AllComponents.Z_INDEX.value: 3,
        AllComponents.TIMEPOINT.value: 4,
        AllComponents.WELL.value: "A01",
        SourceFilterSubject.EXTENSION.value: ".tif",
    }
    projection = VirtualWorkspaceSourceProjection(
        source_refs_by_virtual_path={virtual_path: source_ref},
        source_metadata_by_path={virtual_path: source_metadata},
        source_projections_by_virtual_path={
            virtual_path: SourcePlaneProjection(
                address=OpenHCSPlaneAddress.from_values(
                    well="A01",
                    site="2",
                    channel="1",
                    z_index="3",
                    timepoint="4",
                ),
                ref=source_ref,
                source_alias="OrigDNA",
                source_metadata=source_metadata,
            ),
        },
        workspace_root=str(tmp_path),
    )

    class SourceFileManager:
        @staticmethod
        def resolve_address(backend_address, backend, *, base_path):
            del base_path
            assert backend == source_ref.backend
            assert backend_address == source_ref.backend_address
            return backend_address

        physical_source_path = resolve_address

    runtime = PatternGroupExecutionRequest(
        context=SimpleNamespace(filemanager=SourceFileManager()),
        execution_plan=CompiledStepPlan(
            step_index=0,
            step_name="source fixture",
            step_type="FunctionStep",
            axis_id="A01",
            source_binding_plan=CompiledSourceBindingPlan(
                bindings=(NamedSourceBinding(alias="FilenamePrefix"),),
            ),
        ),
        compiled_group=compile_function_pattern(
            lambda image: image, {}, {}
        ).default_group,
        pattern_group_info="fixture",
        component_index=0,
        component_count=1,
    )
    payload = ImagePayloadMetadata(source_path=full_virtual_path).payload_with(
        np.zeros((4, 5), dtype=np.uint16),
        None,
    )

    lookup = VirtualWorkspacePathLookup.from_paths(virtual_path, full_virtual_path)
    workspace_source_lookups = runtime._workspace_source_binding_lookups(
        projection,
        (lookup,),
    )
    assert workspace_source_lookups == ()

    (projected,) = runtime._apply_source_image_loading_semantics(
        (payload,),
        (lookup,),
        workspace_source_lookups,
        projection,
    )

    assert image_payload_metadata(projected).source_component_metadata == {
        AllComponents.SITE.value: 2,
        AllComponents.CHANNEL.value: 1,
        AllComponents.Z_INDEX.value: 3,
        AllComponents.TIMEPOINT.value: 4,
        AllComponents.WELL.value: "A01",
        SourceFilterSubject.EXTENSION.value: ".tif",
    }
    assert image_payload_metadata(
        projected
    ).source_provenance.represented_source_image_names == ("OrigDNA",)


def test_step_output_load_filter_skips_source_binding_filter() -> None:
    from openhcs.core.steps.function_runtime import PatternGroupExecutionRequest

    plan = SimpleNamespace(
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=4,
            source_step_scope_id="mask_image",
        ),
        source_binding_plan=CompiledSourceBindingPlan(
            bindings=(NamedSourceBinding(alias="OrigDNA"),)
        ),
    )
    runtime = PatternGroupExecutionRequest(
        execution_plan=plan,
        context=SimpleNamespace(),
        compiled_group=compile_function_pattern(
            lambda image: image, {}, {}
        ).default_group,
        pattern_group_info="fixture",
        component_index=0,
        component_count=1,
    )
    matching_files = ["/tmp/outputs/A14_s001_w3_z001_t001.tif"]

    assert (
        runtime._filter_matching_files_for_source_bindings(matching_files)
        is matching_files
    )


def test_empty_source_binding_plan_does_not_filter_runtime_inputs() -> None:
    from openhcs.core.steps.function_runtime import (
        PatternGroupExecutionRequest,
    )

    compiled_pattern = compile_function_pattern(lambda image: image, {}, {})
    plan = SimpleNamespace(
        axis_id="A01",
        execution_group_scope=ComponentGroupScope.ungrouped(),
        main_input_dependency=StepInputDependency.pipeline_start(),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
    )
    runtime = PatternGroupExecutionRequest(
        context=SimpleNamespace(),
        execution_plan=plan,
        compiled_group=compiled_pattern.default_group,
        component_value=None,
        pattern_group_info="A14_s001_w3_z001_t001.tif",
        component_index=0,
        component_count=1,
    )
    matching_files = ["/tmp/outputs/A14_s001_w3_z001_t001.tif"]

    assert (
        runtime._filter_matching_files_for_source_bindings(matching_files)
        is matching_files
    )


def test_producer_anchored_pipeline_start_paths_use_exact_source_projection_bundle(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    """Producer bookkeeping must not override exact workspace source ownership."""

    from openhcs.core.steps import function_runtime
    from openhcs.core.runtime_source_binding_cache import (
        RuntimeSourceBindingContextCache,
    )

    virtual_paths = (
        "A01_s001_w1_z001_t001.tif",
        "A01_s001_w2_z001_t001.tif",
    )
    aliases = ("OrigColor", "PlateTemplate")
    source_paths = (
        tmp_path / "source" / "color.tif",
        tmp_path / "source" / "template.tif",
    )
    source_planes = tuple(
        SourcePlaneProjection(
            address=OpenHCSPlaneAddress.from_values(
                well="A01",
                site="1",
                channel=str(channel),
                z_index="1",
                timepoint="1",
            ),
            ref=SourcePixelRef("disk", str(source_path)),
            source_alias=alias,
        )
        for channel, alias, source_path in zip(
            (1, 2),
            aliases,
            source_paths,
            strict=True,
        )
    )
    projection = VirtualWorkspaceSourceProjection(
        source_refs_by_virtual_path={
            virtual_path: source_plane.ref
            for virtual_path, source_plane in zip(
                virtual_paths,
                source_planes,
                strict=True,
            )
        },
        source_metadata_by_path={
            virtual_paths[0]: {
                SOURCE_BINDING_ALIAS_METADATA_FIELD: aliases[0],
                "specimen": "sample",
            },
            virtual_paths[1]: {
                SOURCE_BINDING_ALIAS_METADATA_FIELD: aliases[1],
            },
        },
        source_projections_by_virtual_path={
            virtual_path: source_plane
            for virtual_path, source_plane in zip(
                virtual_paths,
                source_planes,
                strict=True,
            )
        },
        workspace_root=str(tmp_path),
    )
    source_binding_plan = CompiledSourceBindingPlan(
        bindings=(
            NamedSourceBinding(
                alias="OrigColor",
                source_channel_axis=-1,
                source_channel_counts=frozenset({3}),
            ),
            NamedSourceBinding(alias="PlateTemplate"),
        )
    )

    class SourceFileManager:
        @staticmethod
        def load_batch(paths, backend):
            assert backend == "memory"
            payloads = {
                virtual_paths[0]: np.arange(60, dtype=np.float32).reshape(4, 5, 3),
                virtual_paths[1]: np.full((4, 5), 7, dtype=np.float32),
            }
            return [payloads[Path(path).name] for path in paths]

        @staticmethod
        def resolve_address(backend_address, backend, *, base_path):
            del base_path
            assert backend == "disk"
            return backend_address

        physical_source_path = resolve_address

    monkeypatch.setattr(
        function_runtime,
        "step_output_manifest",
        lambda _context: StepOutputManifestStore(),
    )
    monkeypatch.setattr(
        function_runtime.PatternGroupExecutionRequest,
        "source_workspace_projection_authority",
        lambda _self: SimpleNamespace(
            projection_if_available=lambda: projection,
            projection_or_empty=lambda: projection,
        ),
    )

    compiled_pattern = compile_function_pattern(lambda image: image, {}, {})
    plan = CompiledStepPlan(
        step_index=0,
        step_name="PipelineStart",
        step_type="FunctionStep",
        axis_id="A01",
        input_dir=tmp_path,
        read_backend="memory",
        input_memory_type="numpy",
        variable_components=(),
        main_input_dependency=StepInputDependency.pipeline_start(),
        source_binding_plan=source_binding_plan,
    )
    context = SimpleNamespace(
        microscope_handler=SimpleNamespace(
            parser=SourceSchemaFilenameParser(),
            path_list_from_pattern=lambda *_args, **_kwargs: list(virtual_paths),
        ),
        filemanager=SourceFileManager(),
        runtime_image_stack_cache=RuntimeImageStackCache(),
        runtime_pattern_discovery_cache=RuntimePatternDiscoveryCache(),
        runtime_source_binding_context_cache=RuntimeSourceBindingContextCache(),
        runtime_source_workspace_projection_cache=(
            VirtualWorkspaceSourceProjectionCache()
        ),
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )
    runtime = function_runtime.PatternGroupExecutionRequest(
        context=context,
        execution_plan=plan,
        compiled_group=compiled_pattern.default_group,
        pattern_group_info="A01_s001_w{iii}_z001_t001.tif",
        component_index=0,
        component_count=1,
    )
    monkeypatch.setattr(
        type(runtime),
        "_source_binding_load_universe",
        lambda _request, *args, **kwargs: (lambda: virtual_paths)(*args, **kwargs),
    )

    loaded = runtime.load_input_stack()

    data = image_payload_data(loaded[1])
    metadata = image_payload_metadata(loaded[1])
    assert data.shape == (2, 4, 5, 3)
    np.testing.assert_array_equal(data[1], np.full((4, 5, 3), 7, dtype=np.float32))
    assert metadata.source_image_names == aliases
    assert metadata.plane_axis is RuntimePlaneAxis.SOURCE_BINDING
    assert metadata.source_channel_axis == 3
    assert metadata.source_component_metadata["specimen"] == "sample"


def test_step_output_load_preserves_producer_stack_plane_provenance(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    """Derived stacks must not be rebound as pipeline-source images on load."""

    from openhcs.core.steps import function_runtime

    output_path = tmp_path / "A01_s001_w2_z001_t001_RescaledDNA.tif"
    producer_payload = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=(str(output_path), str(output_path)),
            component_metadata=(
                {
                    "well": "A01",
                    "site": "1",
                    "channel": "2",
                    "z_index": "1",
                    "timepoint": "1",
                },
                {
                    "well": "A01",
                    "site": "1",
                    "channel": "2",
                    "z_index": "2",
                    "timepoint": "1",
                },
            ),
        ),
    ).payload_with(np.zeros((2, 4, 5), dtype=np.float32), None)

    class MemoryFileManager:
        def load_batch(self, paths, backend):
            assert paths == [str(output_path)]
            assert backend == "memory"
            return [producer_payload]

    monkeypatch.setattr(
        function_runtime,
        "step_output_manifest",
        lambda _context: producer_manifest,
    )
    monkeypatch.setattr(
        function_runtime.PatternGroupExecutionRequest,
        "source_workspace_projection_authority",
        lambda _self: SimpleNamespace(
            projection_if_available=lambda: VirtualWorkspaceSourceProjection.empty()
        ),
    )
    monkeypatch.setattr(
        function_runtime.PatternGroupExecutionRequest,
        "_filter_matching_files_for_group",
        lambda _self, paths: paths,
    )
    monkeypatch.setattr(
        function_runtime.PatternGroupExecutionRequest,
        "_filter_matching_files_for_source_bindings",
        lambda _self, paths: paths,
    )
    plan = CompiledStepPlan(
        step_index=1,
        step_name="Resize",
        step_type="FunctionStep",
        axis_id="A01",
        input_dir=tmp_path,
        input_memory_type="numpy",
        variable_components=(VariableComponents.Z_INDEX,),
        compiled_function_pattern=compile_function_pattern(lambda image: image, {}, {}),
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=0,
            source_step_scope_id="producer",
        ),
    )
    producer = CompiledStepPlan(
        step_index=0,
        step_name="producer",
        step_type="FunctionStep",
        step_scope_id="producer",
        axis_id="A01",
        output_dir=tmp_path,
    )
    producer_manifest = StepOutputManifestStore()
    producer_manifest.begin_step(producer)
    producer_manifest.record_outputs(
        producer,
        (
            ProducedOutputSemantics.from_output(
                producer,
                output_path,
                FunctionOutputIdentity(
                    component_values={
                        "well": "A01",
                        "site": "1",
                        "channel": "2",
                        "z_index": "1",
                        "timepoint": "1",
                    },
                    extension=".tif",
                    source="test",
                ),
            ).with_filename_qualifier("RescaledDNA"),
        ),
    )
    context = SimpleNamespace(
        microscope_handler=SimpleNamespace(parser=SourceSchemaFilenameParser()),
        filemanager=MemoryFileManager(),
        runtime_image_stack_cache=RuntimeImageStackCache(),
    )
    runtime = PatternGroupExecutionRequest(
        context=context,
        execution_plan=replace(
            plan, source_binding_plan=CompiledSourceBindingPlan.empty()
        ),
        compiled_group=plan.compiled_function_pattern.default_group,
        pattern_group_info="A01_s001_w2_z{iii}_t001.tif",
        component_index=0,
        component_count=1,
    )

    loaded = runtime.load_input_stack()

    provenance_planes = image_payload_metadata(loaded[1]).source_image_provenance_planes
    assert provenance_planes.count == 2
    assert provenance_planes.contributor_count == 0
    plane_metadata = provenance_planes.component_metadata
    assert tuple(metadata["z_index"] for metadata in plane_metadata) == ("1", "2")


def test_artifact_managed_group_uses_compiler_group_without_filtering_anchor_files() -> (
    None
):
    from openhcs.core.steps.function_runtime import PatternGroupExecutionRequest

    runtime = PatternGroupExecutionRequest(
        compiled_group=SimpleNamespace(
            runtime_domain=RuntimeInvocationDomain.ARTIFACT_MANAGED,
        ),
        execution_plan=CompiledStepPlan(
            step_index=0,
            step_name="source fixture",
            step_type="FunctionStep",
            axis_id="A01",
            main_input_dependency=StepInputDependency.pipeline_start(),
        ),
        component_value="1",
        context=SimpleNamespace(),
        pattern_group_info="fixture",
        component_index=0,
        component_count=1,
    )
    matching_files = ["/tmp/outputs/A01_s001_w2_z001_t001.tif"]

    assert runtime._filter_matching_files_for_group(matching_files) is matching_files


def test_step_output_group_does_not_reinterpret_producer_path_component() -> None:
    from openhcs.core.steps.function_runtime import PatternGroupExecutionRequest

    runtime = PatternGroupExecutionRequest(
        compiled_group=SimpleNamespace(
            runtime_domain=RuntimeInvocationDomain.SOURCE_ANCHORED,
        ),
        execution_plan=CompiledStepPlan(
            step_index=0,
            step_name="source fixture",
            step_type="FunctionStep",
            axis_id="A01",
            main_input_dependency=StepInputDependency.step_output(
                source_step_index=4,
                source_step_scope_id="object_to_image",
            ),
        ),
        component_value="0",
        context=SimpleNamespace(),
        pattern_group_info="fixture",
        component_index=0,
        component_count=1,
    )
    matching_files = ["/tmp/outputs/A01_s001_w2_z001_t001.tif"]

    assert runtime._filter_matching_files_for_group(matching_files) is matching_files


def test_ungrouped_runtime_scope_omits_axis_component() -> None:
    from openhcs.core.steps.function_runtime import PatternGroupExecutionScope

    scope = PatternGroupExecutionScope(
        context=SimpleNamespace(),
        execution_plan=SimpleNamespace(
            axis_id="A01",
            group_by_value=GroupBy.CHANNEL.value,
            execution_group_value=None,
        ),
        compiled_group=SimpleNamespace(),
        component_value=None,
    )

    assert scope.axis_component is None
    assert scope.axis_component_value is None
    assert scope.axis_scope.component is None
    assert scope.axis_scope.value is None


def test_step_output_manifest_does_not_filter_main_flow_by_artifact_input(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "images"
    producer = CompiledStepPlan(
        step_index=1,
        step_type="FunctionStep",
        step_scope_id="correct_illumination",
        step_name="CorrectIlluminationApply",
        pipeline_position=1,
        axis_id="A01",
        output_dir=output_dir,
    )
    consumer = SimpleNamespace(
        axis_id="A01",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=1,
            source_step_scope_id="correct_illumination",
        ),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
        artifact_inputs={
            plan.ref(): plan
            for plan in (
                ArtifactInputPlan(
                    name="CorrDNA",
                    path="CorrDNA",
                    artifact_type=ImageArtifactType,
                    source_step_id=1,
                ),
            )
        },
        compiled_function_pattern=compile_function_pattern(lambda image: image, {}, {}),
    )
    store = StepOutputManifestStore()

    store.begin_step(producer)
    store.record_outputs(
        producer,
        (
            ProducedOutputSemantics.from_output(
                producer,
                output_dir / "A01_s001_w1_z001_t001.tif",
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
                    output_key="CorrProtein",
                    artifact_kind=ImageArtifactType.value,
                ),
            ),
            ProducedOutputSemantics.from_output(
                producer,
                output_dir / "A01_s001_w2_z001_t001.tif",
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
                    output_key="CorrDNA",
                    artifact_kind=ImageArtifactType.value,
                ),
            ),
        ),
    )

    assert store.filter_to_producer_paths(
        consumer,
        [
            "A01_s001_w1_z001_t001.tif",
            "A01_s001_w2_z001_t001.tif",
        ],
        SourceSchemaFilenameParser(),
    ) == [
        "A01_s001_w1_z001_t001.tif",
        "A01_s001_w2_z001_t001.tif",
    ]


def test_step_output_manifest_filters_declared_main_flow_contract_identity(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "images"
    producer = CompiledStepPlan(
        step_index=2,
        step_type="FunctionStep",
        step_scope_id="align",
        step_name="Align",
        pipeline_position=2,
        axis_id="A01",
        output_dir=output_dir,
    )
    input_spec = ArtifactSpec.input("Stain1", ImageArtifactType)

    @artifact_inputs(input_spec)
    def identify_stain_1(image):
        return image

    compiled_pattern = compile_function_pattern(identify_stain_1, {}, {})
    invocation = compiled_pattern.default_group.invocations[0]
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
    compiled_pattern = replace(
        compiled_pattern,
        groups=(
            replace(
                compiled_pattern.default_group,
                invocations=(invocation,),
            ),
        ),
    )
    consumer = SimpleNamespace(
        axis_id="A01",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=2,
            source_step_scope_id="align",
        ),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
        artifact_inputs={},
        compiled_function_pattern=compiled_pattern,
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
    contexts = store.producer_output_contexts_for_paths(
        consumer,
        ("A01_s001_w1_z001_t001.tif",),
        SourceSchemaFilenameParser(),
    )
    assert tuple(context.output_key for context in contexts) == ("Stain1",)


def test_step_output_manifest_updates_selected_slot_and_preserves_other_components(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "images"
    producer = CompiledStepPlan(
        step_index=1,
        step_type="FunctionStep",
        step_scope_id="producer",
        step_name="Producer",
        pipeline_position=1,
        axis_id="A01",
        output_dir=output_dir,
    )
    update = CompiledStepPlan(
        step_index=2,
        step_type="FunctionStep",
        step_scope_id="update",
        step_name="Update",
        pipeline_position=2,
        axis_id="A01",
        output_dir=output_dir,
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=1,
            source_step_scope_id="producer",
        ),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
        artifact_inputs={},
        compiled_function_pattern=compile_function_pattern(lambda image: image, {}, {}),
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
            for channel, output_key in ((1, "Image1"), (2, "Image2"))
        ),
    )

    store.begin_step(update, store.producer_records_for(update) or ())
    store.record_outputs(
        update,
        (
            ProducedOutputSemantics.from_output(
                update,
                output_dir / "A01_s001_w1_z001_t001.tif",
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
                    output_key="Image1",
                    artifact_kind=ImageArtifactType.value,
                ),
            ),
        ),
    )

    records = store.produced_records_for(update)
    assert tuple(record.output_context.output_key for record in records) == (
        "Image1",
        "Image2",
    )
    assert records[0].producer_identity.step_scope_id == "update"
    assert records[1].producer_identity.step_scope_id == "producer"


@pytest.mark.parametrize(
    ("func", "collapsed_input_domain"),
    (
        pytest.param(lambda image: image, True, id="runtime-cardinality"),
        pytest.param(_compose_image_domain, False, id="callable-contract"),
    ),
)
def test_step_output_manifest_collapsed_domain_replaces_inherited_components(
    tmp_path: Path,
    func: Callable,
    collapsed_input_domain: bool,
) -> None:
    output_dir = tmp_path / "images"
    producer = CompiledStepPlan(
        step_index=1,
        step_type="FunctionStep",
        step_scope_id="producer",
        step_name="Producer",
        pipeline_position=1,
        axis_id="A01",
        output_dir=output_dir,
    )
    collapse = CompiledStepPlan(
        step_index=2,
        step_type="FunctionStep",
        step_scope_id="collapse",
        step_name="Collapse",
        pipeline_position=2,
        axis_id="A01",
        output_dir=output_dir,
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=1,
            source_step_scope_id="producer",
        ),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
        artifact_inputs={},
        compiled_function_pattern=compile_function_pattern(func, {}, {}),
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
            )
            for channel in (1, 2, 3)
        ),
    )

    store.begin_step(collapse, store.producer_records_for(collapse) or ())
    store.record_outputs(
        collapse,
        (
            ProducedOutputSemantics.from_output(
                collapse,
                output_dir / "A01_s001_w1_z001_t001.tif",
                FunctionOutputIdentity(
                    component_values={"well": "A01", "site": 1, "channel": 1},
                    extension=".tif",
                    source="test",
                ),
            ),
        ),
        collapsed_input_domain=collapsed_input_domain,
    )

    records = store.produced_records_for(collapse)
    assert len(records) == 1
    assert records[0].producer_identity.step_scope_id == "collapse"


def test_step_output_manifest_new_output_address_replaces_inherited_components(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "images"
    producer = CompiledStepPlan(
        step_index=1,
        step_type="FunctionStep",
        step_scope_id="producer",
        step_name="Producer",
        pipeline_position=1,
        axis_id="A01",
        output_dir=output_dir,
    )
    replacement = CompiledStepPlan(
        step_index=2,
        step_type="FunctionStep",
        step_scope_id="replacement",
        step_name="Replacement",
        pipeline_position=2,
        axis_id="A01",
        output_dir=output_dir,
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=1,
            source_step_scope_id="producer",
        ),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
        artifact_inputs={},
        compiled_function_pattern=compile_function_pattern(lambda image: image, {}, {}),
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
            for channel, output_key in ((1, "Image1"), (2, "Image2"))
        ),
    )

    store.begin_step(replacement, store.producer_records_for(replacement) or ())
    store.record_outputs(
        replacement,
        (
            ProducedOutputSemantics.from_output(
                replacement,
                output_dir / "A01_s001_w1_z001_t001_Projected.tif",
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
                    output_key="Projected",
                    artifact_kind=ImageArtifactType.value,
                ),
            ),
        ),
    )

    records = store.produced_records_for(replacement)
    assert tuple(record.output_context.output_key for record in records) == (
        "Projected",
    )
    assert records[0].producer_identity.step_scope_id == "replacement"


def test_step_output_manifest_grouped_subset_replaces_inherited_components(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "images"
    producer = CompiledStepPlan(
        step_index=1,
        step_type="FunctionStep",
        step_scope_id="producer",
        step_name="Producer",
        pipeline_position=1,
        axis_id="A01",
        output_dir=output_dir,
    )
    subset = CompiledStepPlan(
        step_index=2,
        step_type="FunctionStep",
        step_scope_id="subset",
        step_name="Subset",
        pipeline_position=2,
        axis_id="A01",
        output_dir=output_dir,
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=1,
            source_step_scope_id="producer",
        ),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
        artifact_inputs={},
        compiled_function_pattern=compile_function_pattern(
            {"2": lambda image: image},
            {},
            {},
        ),
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
            )
            for channel in (1, 2)
        ),
    )

    store.begin_step(subset, store.producer_records_for(subset) or ())
    store.record_outputs(
        subset,
        (
            ProducedOutputSemantics.from_output(
                subset,
                output_dir / "A01_s001_w2_z001_t001.tif",
                FunctionOutputIdentity(
                    component_values={"well": "A01", "site": 1, "channel": 2},
                    extension=".tif",
                    source="test",
                ),
            ),
        ),
    )

    records = store.produced_records_for(subset)
    assert tuple(record.component_values["channel"] for record in records) == (2,)


def test_step_output_manifest_preserves_anonymous_side_effect_main_flow(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "images"
    producer = CompiledStepPlan(
        step_index=2,
        step_type="FunctionStep",
        step_scope_id="identify_primary",
        step_name="IdentifyPrimaryObjects",
        pipeline_position=2,
        axis_id="A01",
        output_dir=output_dir,
    )
    consumer = SimpleNamespace(
        axis_id="A01",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=2,
            source_step_scope_id="identify_primary",
        ),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
        artifact_inputs={
            plan.ref(): plan
            for plan in (
                ArtifactInputPlan(
                    name="Nuclei",
                    path="Nuclei",
                    artifact_type=ObjectLabelsArtifactType,
                    source_step_id=2,
                ),
            )
        },
        compiled_function_pattern=compile_function_pattern(lambda image: image, {}, {}),
    )
    store = StepOutputManifestStore()

    store.begin_step(producer)
    store.record_outputs(
        producer,
        (
            ProducedOutputSemantics.from_output(
                producer,
                output_dir / "A01_s001_w2_z001_t001.tif",
                FunctionOutputIdentity(
                    component_values={
                        "well": "A01",
                        "site": 1,
                        "channel": 2,
                    },
                    extension=".tif",
                    source="test",
                ),
            ),
        ),
    )

    assert store.filter_to_producer_paths(
        consumer,
        ["A01_s001_w2_z001_t001.tif"],
        SourceSchemaFilenameParser(),
    ) == ["A01_s001_w2_z001_t001.tif"]


def test_step_output_manifest_accepts_source_anchor_for_qualified_output(
    tmp_path: Path,
) -> None:
    output_dir = tmp_path / "images"
    producer = CompiledStepPlan(
        step_index=4,
        step_type="FunctionStep",
        step_scope_id="correct_illumination_apply",
        step_name="CorrectIlluminationApply",
        pipeline_position=4,
        axis_id="A01",
        output_dir=output_dir,
    )
    consumer = SimpleNamespace(
        axis_id="A01",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=4,
            source_step_scope_id="correct_illumination_apply",
        ),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
        artifact_inputs={
            plan.ref(): plan
            for plan in (
                ArtifactInputPlan(
                    name="CorrBlue",
                    path="CorrBlue",
                    artifact_type=ImageArtifactType,
                    source_step_id=4,
                ),
            )
        },
        compiled_function_pattern=compile_function_pattern(lambda image: image, {}, {}),
    )
    store = StepOutputManifestStore()
    identity = FunctionOutputIdentity(
        component_values={
            "well": "A01",
            "site": 1,
            "channel": 1,
            "z_index": 1,
            "timepoint": 1,
        },
        extension=".jpg",
        source="test",
    ).with_filename_qualifier("CorrBlue")

    store.begin_step(producer)
    store.record_outputs(
        producer,
        (
            ProducedOutputSemantics.from_output(
                producer,
                output_dir / "A01_s001_w1_z001_t001_CorrBlue.jpg",
                identity,
                output_context=AlignedImageSliceContext.main_flow(
                    output_key="CorrBlue",
                    artifact_kind=ImageArtifactType.value,
                ),
            ),
        ),
    )

    assert store.filter_to_producer_paths(
        consumer,
        ["A01_s001_w1_z001_t001.jpg"],
        SourceSchemaFilenameParser(),
    ) == ["A01_s001_w1_z001_t001.jpg"]


def test_function_output_path_uses_payload_identity_over_input_carrier(
    tmp_path: Path,
) -> None:
    payload = ImagePayloadMetadata(
        source_path="/source/plate1_A14_site2_Ch3.tif",
        source_component_metadata={
            "well": "A14",
            "site": "2",
            "channel": "3",
        },
    ).payload_with(np.zeros((4, 5), dtype=np.float32), None)

    output_path = FunctionOutputIdentity.path_from_request(FunctionOutputPathRequest(
            parser=SourceSchemaFilenameParser(),
            output_dir=tmp_path,
            output_payload=payload,
            input_path="A14_s001_w1_z001_t001.tif",
        ))

    assert output_path.name == "A14_s002_w3_z001_t001.tif"


def test_function_output_path_uses_payload_identity_without_input_path(
    tmp_path: Path,
) -> None:
    payload = ImagePayloadMetadata(
        source_path="/source/plate1_A14_site1_Ch5.tif",
        source_component_metadata={
            "well": "A14",
            "site": "1",
            "channel": "5",
            "z_index": "1",
            "timepoint": "1",
        },
    ).payload_with(np.zeros((4, 5), dtype=np.float32), None)

    output_path = FunctionOutputIdentity.path_from_request(FunctionOutputPathRequest(
            parser=SourceSchemaFilenameParser(),
            output_dir=tmp_path,
            output_payload=payload,
            input_path=None,
        ))

    assert output_path.name == "A14_s001_w5_z001_t001.tif"


def test_function_output_identity_completes_partial_payload_metadata_from_fallback_path() -> (
    None
):
    parser = SourceSchemaFilenameParser()
    metadata = ImagePayloadMetadata(
        source_component_metadata={
            "well": "Sequence1",
            "site": 1,
            "z_index": 1,
            "channel": 1,
            "extension": ".tif",
        },
    )

    identity = FunctionOutputIdentity.from_metadata(
        parser,
        metadata,
        fallback_identity_path="Sequence1_s001_w1_z001_t000.tif",
    )

    assert identity is not None
    assert (
        identity.filename(parser)
        == "Sequence1_s001_w1_z001_t000.tif"
    )


def test_function_output_identity_uses_fallback_path_extension_for_payload_identity() -> (
    None
):
    parser = SourceSchemaFilenameParser()
    metadata = ImagePayloadMetadata(
        source_component_metadata={
            "well": "A01",
            "site": 1,
            "z_index": 1,
            "timepoint": 1,
            "channel": 2,
        },
    )

    identity = FunctionOutputIdentity.from_metadata(
        parser,
        metadata,
        fallback_identity_path="A01_s001_w1_z001_t001.png",
    )

    assert identity is not None
    assert (
        identity.filename(parser)
        == "A01_s001_w2_z001_t001.png"
    )


def test_function_output_path_uses_input_identity_for_multi_plane_carrier(
    tmp_path: Path,
) -> None:
    payload = ImagePayloadMetadata(
        source_component_metadata={
            "well": "A14",
            "site": "1",
            "channel": "1",
            "timepoint": "1",
            "extension": ".tif",
        },
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=(
                "/source/A14_s001_w1_z001_t001.tif",
                "/source/A14_s001_w2_z001_t001.tif",
            ),
            component_metadata=(
                {"well": "A14", "site": "1", "channel": "1"},
                {"well": "A14", "site": "1", "channel": "2"},
            ),
        ),
    ).payload_with(np.zeros((2, 4, 5), dtype=np.float32), None)

    output_path = FunctionOutputIdentity.path_from_request(FunctionOutputPathRequest(
            parser=SourceSchemaFilenameParser(),
            output_dir=tmp_path,
            output_payload=payload,
            input_path="A14_s001_w1_z001_t001.tif",
        ))

    assert output_path.name == "A14_s001_w1_z001_t001.tif"


def test_function_output_path_rejects_multi_plane_carrier_without_input_path(
    tmp_path: Path,
) -> None:
    payload = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=(
                "/source/A14_s001_w1_z001_t001.tif",
                "/source/A14_s001_w2_z001_t001.tif",
            ),
        ),
    ).payload_with(np.zeros((2, 4, 5), dtype=np.float32), None)

    with pytest.raises(ValueError, match="multi-plane source provenance"):
        FunctionOutputIdentity.path_from_request(FunctionOutputPathRequest(
                parser=SourceSchemaFilenameParser(),
                output_dir=tmp_path,
                output_payload=payload,
                input_path=None,
            ))


def test_function_output_path_uses_variable_component_identity(
    tmp_path: Path,
) -> None:
    payload = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=(
                "/source/A14_s001_w1_z001_t001.tif",
                "/source/A14_s001_w1_z002_t001.tif",
            ),
            component_metadata=(
                {
                    "well": "A14",
                    "site": "1",
                    "channel": "1",
                    "z_index": "1",
                    "timepoint": "1",
                },
                {
                    "well": "A14",
                    "site": "1",
                    "channel": "1",
                    "z_index": "2",
                    "timepoint": "1",
                },
            ),
        ),
    ).payload_with(np.zeros((2, 4, 5), dtype=np.float32), None)
    request = FunctionOutputPathRequest(
        parser=SourceSchemaFilenameParser(),
        output_dir=tmp_path,
        output_payload=payload,
        input_path=None,
        variable_components=(VariableComponents.Z_INDEX,),
    )

    identity = FunctionOutputIdentity.from_request(request)
    output_path = identity.path_for_request(request)

    assert output_path.name == "A14_s001_w1_z001_t001.tif"
    assert identity.component_values == {
        "well": "A14",
        "site": 1,
        "channel": 1,
        "timepoint": 1,
    }
    assert identity.filename_component_values is not None
    assert identity.filename_component_values["z_index"] == 1


def test_collapsed_output_identity_uses_retained_source_contributors(
    tmp_path: Path,
) -> None:
    stack_metadata = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=(
                "/source/A14_s001_w1_z001_t001.tif",
                "/source/A14_s002_w1_z001_t001.tif",
            ),
            component_metadata=(
                {
                    "well": "A14",
                    "site": "1",
                    "channel": "1",
                    "z_index": "1",
                    "timepoint": "1",
                },
                {
                    "well": "A14",
                    "site": "2",
                    "channel": "1",
                    "z_index": "1",
                    "timepoint": "1",
                },
            ),
        ),
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    )
    collapsed_metadata = stack_metadata.collapse_leading_plane_axis()
    payload = collapsed_metadata.payload_with(
        np.zeros((4, 5), dtype=np.float32),
        None,
    )
    request = FunctionOutputPathRequest(
        parser=SourceSchemaFilenameParser(),
        output_dir=tmp_path,
        output_payload=payload,
        input_path=None,
        variable_components=(VariableComponents.SITE,),
    )

    identity = FunctionOutputIdentity.from_request(request)
    filename_identity = FunctionOutputIdentity.from_filename_metadata(
        request.parser,
        collapsed_metadata,
    )
    output_path = identity.path_for_request(request)

    assert collapsed_metadata.source_image_provenance_planes.count == 0
    assert collapsed_metadata.source_image_provenance_planes.contributor_count == 2
    assert output_path.name == "A14_s001_w1_z001_t001.tif"
    assert identity.component_values == {
        "well": "A14",
        "channel": 1,
        "z_index": 1,
        "timepoint": 1,
    }
    assert identity.filename_component_values is not None
    assert identity.filename_component_values["site"] == 1
    assert filename_identity is not None
    assert (
        filename_identity.filename(request.parser)
        == "A14_s001_w1_z001_t001.tif"
    )


def test_composite_then_z_collapse_uses_current_scalar_identity(
    tmp_path: Path,
) -> None:
    composite_payloads = []
    for z_index in (1, 2, 3):
        channel_stack_metadata = ImagePayloadMetadata(
            source_image_provenance_planes=(
                SourceImageProvenancePlanes.from_components(
                    paths=tuple(
                        f"/source/A01_s001_w{channel}_z{z_index:03d}_t001.tif"
                        for channel in (1, 2)
                    ),
                    component_metadata=tuple(
                        {
                            "well": "A01",
                            "site": "1",
                            "channel": str(channel),
                            "z_index": str(z_index),
                            "timepoint": "1",
                        }
                        for channel in (1, 2)
                    ),
                )
            ),
            plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        )
        composite_payloads.append(
            channel_stack_metadata.collapse_leading_plane_axis().payload_with(
                np.zeros((4, 5), dtype=np.float32),
                None,
            )
        )

    z_stack_metadata = ImagePayloadMetadata.compose(composite_payloads)
    projected_metadata = z_stack_metadata.collapse_leading_plane_axis()
    payload = projected_metadata.payload_with(
        np.zeros((4, 5), dtype=np.float32),
        None,
    )
    request = FunctionOutputPathRequest(
        parser=SourceSchemaFilenameParser(),
        output_dir=tmp_path,
        output_payload=payload,
        input_path="A01_s001_w1_z001_t001.tif",
        variable_components=(VariableComponents.Z_INDEX,),
    )

    identity = FunctionOutputIdentity.from_request(request)
    output_path = identity.path_for_request(request)

    assert z_stack_metadata.source_provenance.source_plane_count == 3
    assert projected_metadata.source_provenance.source_plane_count == 0
    assert projected_metadata.source_image_provenance_planes.contributor_count == 6
    assert identity.component_values == {
        "well": "A01",
        "site": 1,
        "timepoint": 1,
    }
    assert identity.filename_component_values is not None
    assert identity.filename_component_values["channel"] == 1
    assert identity.filename_component_values["z_index"] == 1
    assert output_path.name == "A01_s001_w1_z001_t001.tif"


def test_variable_component_identity_uses_fallback_path_extension(
    tmp_path: Path,
) -> None:
    payload = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=(
                "/source/A01_s001_w1_z001_t001.png",
                "/source/A01_s001_w2_z001_t001.jpg",
                "/source/A01_s001_w3_z001_t001.jpg",
            ),
        ),
    ).payload_with(np.zeros((3, 4, 5), dtype=np.float32), None)
    request = FunctionOutputPathRequest(
        parser=SourceSchemaFilenameParser(),
        output_dir=tmp_path,
        output_payload=payload,
        input_path="A01_s001_w2_z001_t001.png",
        variable_components=(VariableComponents.CHANNEL,),
    )

    identity = FunctionOutputIdentity.from_request(request)
    output_path = identity.path_for_request(request)

    assert output_path.name == "A01_s001_w1_z001_t001.png"
    assert identity.extension == ".png"
    assert identity.component_values == {
        "well": "A01",
        "site": 1,
        "z_index": 1,
        "timepoint": 1,
    }


def test_declared_main_flow_output_context_qualifies_output_filename(
    tmp_path: Path,
) -> None:
    payload = ImagePayloadMetadata(
        source_path="/source/A01_s001_w1_z001_t001.jpg",
    ).payload_with(np.zeros((4, 5), dtype=np.float32), None)
    request = FunctionOutputPathRequest(
        parser=SourceSchemaFilenameParser(),
        output_dir=tmp_path,
        output_payload=payload,
        input_path="A01_s001_w1_z001_t001.jpg",
    )
    identity = FunctionOutputIdentity.from_request(request)

    red_path = identity.with_filename_qualifier("CorrRed").path_for_request(request)
    green_path = identity.with_filename_qualifier("CorrGreen").path_for_request(request)

    assert red_path.name == "A01_s001_w1_z001_t001_CorrRed.jpg"
    assert green_path.name == "A01_s001_w1_z001_t001_CorrGreen.jpg"
    parsed = SourceSchemaFilenameParser().parse_filename(red_path.name)
    assert parsed is not None
    assert dict(parsed.wire_mapping()) == {
        "well": "A01",
        "site": 1,
        "channel": 1,
        "z_index": 1,
        "timepoint": 1,
        "extension": ".jpg",
    }


def test_function_output_path_rejects_variation_outside_identity_components(
    tmp_path: Path,
) -> None:
    payload = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=(
                "/source/A14_s001_w1_z001_t001.tif",
                "/source/A14_s001_w2_z002_t001.tif",
            ),
        ),
    ).payload_with(np.zeros((2, 4, 5), dtype=np.float32), None)

    assert image_payload_metadata(payload).source_provenance.source_plane_count == 2
    assert (
        image_payload_metadata(payload).source_image_provenance_planes.contributor_count
        == 0
    )

    with pytest.raises(ValueError, match="varies outside identity components"):
        FunctionOutputIdentity.from_request(
            FunctionOutputPathRequest(
                parser=SourceSchemaFilenameParser(),
                output_dir=tmp_path,
                output_payload=payload,
                input_path=None,
                variable_components=(VariableComponents.Z_INDEX,),
            )
        )


def test_function_output_path_rejects_group_by_component_stack_variation(
    tmp_path: Path,
) -> None:
    payload = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=(
                "/source/A01_s001_w1_z001_t001.tif",
                "/source/A01_s001_w3_z001_t001.tif",
                "/source/A01_s001_w2_z001_t001.tif",
            ),
        ),
    ).payload_with(np.zeros((3, 4, 5), dtype=np.float32), None)
    with pytest.raises(ValueError, match="varies outside identity components"):
        FunctionOutputIdentity.from_request(
            FunctionOutputPathRequest(
                parser=SourceSchemaFilenameParser(),
                output_dir=tmp_path,
                output_payload=payload,
                input_path=None,
                variable_components=(VariableComponents.SITE,),
            )
        )


def test_input_aligned_stack_output_uses_input_filename_identity(
    tmp_path: Path,
) -> None:
    payload = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=(
                "/source/A01_s001_w1_z001_t001.png",
                "/source/A01_s002_w1_z001_t001.png",
            ),
        ),
    ).payload_with(np.zeros((2, 4, 5), dtype=np.float32), None)
    request = FunctionOutputPathRequest(
        parser=SourceSchemaFilenameParser(),
        output_dir=tmp_path,
        output_payload=payload,
        input_path="A01_s002_w1_z001_t001.png",
        variable_components=(VariableComponents.SITE,),
        input_aligned_output=True,
    )

    identity = FunctionOutputIdentity.from_request(request)
    output_path = identity.path_for_request(request)

    assert output_path.name == "A01_s002_w1_z001_t001.png"
    assert identity.component_values["site"] == 2
    assert identity.filename_component_values is not None
    assert identity.filename_component_values["site"] == 2


@pytest.mark.parametrize("retains_contributors", [False, True])
def test_function_output_path_keeps_payload_split_axis_over_input_alignment(
    tmp_path: Path,
    retains_contributors: bool,
) -> None:
    payload = ImagePayloadMetadata(
        source_path="/source/A01_s001_w1_z001_t001.tif",
        source_component_metadata={
            "well": "A01",
            "site": "1",
            "channel": "1",
            "z_index": "1",
            "timepoint": "1",
        },
        source_image_provenance_planes=(
            SourceImageProvenancePlanes.from_contributor_components(
                paths=(
                    "/source/A01_s001_w1_z001_t001.tif",
                    "/source/A01_s002_w1_z001_t001.tif",
                ),
                component_metadata=({"site": "1"}, {"site": "2"}),
            )
            if retains_contributors
            else SourceImageProvenancePlanes()
        ),
    ).payload_with(np.zeros((4, 5), dtype=np.float32), None)
    request = FunctionOutputPathRequest(
        parser=SourceSchemaFilenameParser(),
        output_dir=tmp_path,
        output_payload=payload,
        input_path="A01_s003_w1_z001_t001.tif",
        variable_components=(VariableComponents.SITE,),
        input_aligned_output=True,
    )

    identity = FunctionOutputIdentity.from_request(request)
    output_path = identity.path_for_request(request)

    assert output_path.name == "A01_s001_w1_z001_t001.tif"
    assert identity.component_values["site"] == 1
    assert identity.filename_component_values is not None
    assert identity.filename_component_values["site"] == 1


@pytest.mark.parametrize("named_topology", ["anonymous", "unwrapped", "explicit"])
def test_save_outputs_positional_lowering_preserves_explicit_payload_identity(
    tmp_path: Path,
    named_topology: str,
) -> None:
    from openhcs.core.steps.function_runtime import PatternGroupExecutionRequest
    from openhcs.core.runtime_stack_cache import RuntimeImageStackCache
    from openhcs.core.compiled_step_plan import CompiledStepPlan
    from openhcs.core.component_group_scope import ComponentGroupScope
    from openhcs.core.function_patterns import compile_function_pattern
    from openhcs.core.aligned_image_payload import AlignedImageStack

    class OutputFileManager:
        saved_payloads: list[object] = []
        saved_paths: list[str] = []

        @staticmethod
        def exists(_path: str, _backend: str) -> bool:
            return False

        @staticmethod
        def ensure_directory(_path: str, _backend: str) -> None:
            return None

        def save_batch(
            self,
            payloads: list[object],
            paths: list[str],
            _backend: str,
        ) -> None:
            self.saved_payloads = payloads
            self.saved_paths = paths

    output_plans = {}
    func = lambda image: image
    if named_topology != "anonymous":
        spec = ArtifactSpec.output("Corrected", ImageArtifactType)
        output_plan = ArtifactOutputPlan(
            name=spec.name,
            path=str(tmp_path / "Corrected.pkl"),
            artifact_type=spec.artifact_type,
        )
        output_plans[output_plan.ref()] = output_plan
        func = artifact_outputs(spec)(func)
    filemanager = OutputFileManager()
    runtime = PatternGroupExecutionRequest(
        context=SimpleNamespace(
            filemanager=filemanager,
            microscope_handler=SimpleNamespace(
                parser=SourceSchemaFilenameParser(),
            ),
            runtime_function_output_identity_cache=FunctionOutputIdentityCache(),
            runtime_image_stack_cache=RuntimeImageStackCache(),
        ),
        compiled_group=compile_function_pattern(func, {}, output_plans).default_group,
        execution_plan=CompiledStepPlan(
            step_index=0,
            step_type="FunctionStep",
            axis_id="A01",
            output_dir=tmp_path,
            output_memory_type="numpy",
            variable_components=(VariableComponents.SITE,),
            step_name="ExplicitIdentity",
            pipeline_position=0,
            step_scope_id="explicit-identity",
            execution_group_scope=ComponentGroupScope.ungrouped(),
            artifact_outputs=output_plans,
        ),
        pattern_group_info="A01_s{iii}_w1_z001_t001.tif",
        component_value=None,
        component_index=0,
        component_count=1,
    )
    payload = ImagePayloadMetadata(
        source_path="/source/A01_s001_w1_z001_t001.tif",
        source_component_metadata={
            "well": "A01",
            "site": "1",
            "channel": "1",
            "z_index": "1",
            "timepoint": "1",
        },
    ).payload_with(np.zeros((4, 5), dtype=np.float32), None)

    named_context = AlignedImageSliceContext.main_flow(
        "Corrected",
        artifact_kind=ImageArtifactType.value,
    )
    output = (
        AlignedImageStack((payload,), (named_context,))
        if named_topology == "explicit"
        else payload
    )
    records = runtime._save_outputs(
        output,
        ["A01_s003_w1_z001_t001.tif"],
    )

    expected = "A01_s001_w1_z001_t001"
    if named_topology == "explicit":
        expected += "_Corrected"
    assert Path(filemanager.saved_paths[0]).name == expected + ".tif"
    assert (
        image_payload_metadata(filemanager.saved_payloads[0]).source_component_metadata[
            "site"
        ]
        == "1"
    )
    assert records[0].component_values["site"] == 1
    if named_topology != "anonymous":
        assert records[0].output_context == named_context
        assert image_payload_metadata(
            filemanager.saved_payloads[0]
        ).source_image_names == ("Corrected",)
    assert image_payload_data(filemanager.saved_payloads[0]) is image_payload_data(
        payload
    )


@pytest.fixture
def qualified_producer_manifest(tmp_path):
    parser = SourceSchemaFilenameParser()
    producer = CompiledStepPlan(
        step_index=0,
        step_type="FunctionStep",
        step_scope_id="producer",
        step_name="Producer",
        pipeline_position=0,
        axis_id="A01",
        output_dir=tmp_path,
    )
    consumer = SimpleNamespace(
        axis_id="A01",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=0, source_step_scope_id="producer"
        ),
        compiled_function_pattern=compile_function_pattern(lambda image: image, {}, {}),
    )
    records = []
    for plane in (1, 2):
        parsed = parser.parse_filename(f"A01_s001_w2_z{plane:03d}_t001.tif")
        identity = FunctionOutputIdentity(
            component_values=dict(parsed.component_wire_mapping()),
            extension=".tif",
            source="test",
            filename_qualifier=f"Output{plane}",
        )
        records.append(
            ProducedOutputSemantics.from_output(
                producer,
                tmp_path
                / identity.filename(parser),
                identity,
                output_context=AlignedImageSliceContext.main_flow(
                    output_key=f"Output{plane}",
                    artifact_kind=ImageArtifactType.value,
                ),
            )
        )
    store = StepOutputManifestStore()
    store.begin_step(producer)
    store.record_outputs(producer, records)
    return store, producer, consumer, tuple(records), parser


def test_step_output_manifest_batch_lookup_preserves_aliases_order_and_duplicates(
    qualified_producer_manifest,
    monkeypatch,
):
    store, _producer, consumer, records, parser = qualified_producer_manifest
    calls = []
    original = FunctionOutputIdentity.filename

    def count_filename(identity, parser):
        calls.append(identity)
        return original(identity, parser)

    monkeypatch.setattr(
        FunctionOutputIdentity, "filename", count_filename
    )
    paths = (
        records[1].output_path,
        "A01_s001_w2_z001_t001.tif",
        records[1].relative_output_path,
        "A01_s001_w2_z001_t001.tif",
    )
    result = store.producer_output_contexts_for_paths(consumer, paths, parser)
    assert tuple(context.output_key for context in result) == (
        "Output2",
        "Output1",
        "Output2",
        "Output1",
    )
    assert len(calls) == len(records)


def test_produced_identity_owns_filename_and_live_storage_coordinate_cache(
    qualified_producer_manifest,
    tmp_path,
    monkeypatch,
):
    _store, _producer, _consumer, records, parser = qualified_producer_manifest
    storage_components = dict(records[0].component_values)
    storage_components["channel"] = 1
    semantic_components = {**storage_components, "well": "B02", "channel": 9}
    record = replace(
        records[0],
        component_values=semantic_components,
        filename_component_values=storage_components,
    ).with_filename_qualifier(" ./Corrected signal?!.. ")
    cache = FunctionOutputIdentityCache()
    calls = []
    original_construct = parser.construct_filename

    def construct(bound):
        calls.append(bound)
        return original_construct(bound)

    monkeypatch.setattr(parser, "construct_filename", construct)
    first = record.cached_filename(parser, cache)
    assert first == "A01_s001_w1_z001_t001_Corrected_signal.tif"
    assert record.cached_filename(parser, cache) == first
    assert len(calls) == 1
    # The inherited formatter follows the original live storage mapping;
    # semantic producer coordinates and its recorded path are independent.
    storage_components["channel"] = 2
    second = record.cached_filename(parser, cache)
    assert second == "A01_s001_w2_z001_t001_Corrected_signal.tif"
    assert len(calls) == 2
    assert record.component_metadata()["well"] == "B02"
    assert record.component_metadata()["channel"] == "9"
    assert record.output_path == records[0].output_path
    request = FunctionOutputPathRequest(
        parser=parser,
        output_dir=tmp_path / "other",
        output_payload=np.zeros((3, 4), dtype=np.float32),
        input_path=None,
        identity_cache=cache,
    )
    assert record.path_for_request(request) == tmp_path / "other" / second
    assert len(calls) == 2


def test_step_output_manifest_batch_lookup_template_deduplicates_record_aliases(
    qualified_producer_manifest,
):
    store, _producer, consumer, records, parser = qualified_producer_manifest
    path = "{anything}z001{suffix}.tif"
    assert store.producer_output_contexts_for_paths(consumer, (path,), parser) == (
        records[0].output_context,
    )
    index = ProducedPathRecordIndex.from_records(records, parser)
    assert index.contains(path)
    assert index.matching_records(path) == (records[0],)


@pytest.mark.parametrize(
    "path, count",
    [
        ("missing.tif", 0),
        ("A01_s001_w2_z{plane}_t001.tif", 2),
    ],
)
def test_step_output_manifest_batch_lookup_rejects_missing_and_ambiguous_templates(
    qualified_producer_manifest,
    path,
    count,
):
    store, _producer, consumer, _records, parser = qualified_producer_manifest
    with pytest.raises(NoStepOutputManifestMatch, match=f"found {count}"):
        store.producer_output_contexts_for_paths(consumer, (path,), parser)


def test_step_output_manifest_batch_lookup_rejects_shared_basename(
    qualified_producer_manifest,
):
    store, producer, consumer, records, parser = qualified_producer_manifest
    alias = records[0].relative_output_path
    other = ProducedOutputSemantics.from_output(
        producer,
        producer.output_dir / "another" / alias,
        FunctionOutputIdentity(
            component_values=records[1].component_values,
            extension=".tif",
            source="test",
        ),
        output_context=records[1].output_context,
    )
    store.record_outputs(producer, (other,))
    with pytest.raises(NoStepOutputManifestMatch, match="found 2"):
        store.producer_output_contexts_for_paths(consumer, (alias,), parser)
    assert store.producer_output_contexts_for_paths(
        consumer, (records[0].output_path, other.output_path), parser
    ) == (records[0].output_context, other.output_context)


def test_producer_admission_rederives_live_storage_aliases_each_epoch(
    qualified_producer_manifest,
):
    store, producer, consumer, records, parser = qualified_producer_manifest
    storage_components = dict(records[0].filename_values)
    record = replace(records[0], filename_component_values=storage_components).published()
    store.record_outputs(producer, (record,))
    old_index = store.producer_record_index_for(consumer, parser)
    old_alias = record.without_filename_qualifier().filename(parser)
    assert store.filter_to_producer_paths(consumer, (old_alias,), parser) == [old_alias]
    storage_components["channel"] = 9
    new_alias = record.without_filename_qualifier().filename(parser)
    with pytest.raises(NoStepOutputManifestMatch):
        store.filter_to_producer_paths(consumer, (old_alias,), parser)
    assert old_index.matching_records(new_alias) == ()
    current_index = store.producer_record_index_for(consumer, parser)
    assert current_index.matching_records(new_alias) == (record,)
    assert current_index.record_for_path(record.output_path) is record


def test_producer_loader_validates_ambiguity_before_cache(
    monkeypatch,
):
    from openhcs.core.steps import function_runtime

    producer = CompiledStepPlan(
        step_index=0,
        step_name="producer",
        step_type="FunctionStep",
        step_scope_id="producer",
        axis_id="A01",
        output_dir=Path("/memory"),
    )
    plan = CompiledStepPlan(
        step_index=1,
        step_name="consumer",
        step_type="FunctionStep",
        axis_id="A01",
        input_dir=Path("/memory"),
        input_memory_type="numpy",
        compiled_function_pattern=compile_function_pattern(lambda image: image, {}, {}),
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=0,
            source_step_scope_id="producer",
        ),
    )
    manifest = StepOutputManifestStore()
    manifest.begin_step(producer)
    manifest.record_outputs(
        producer,
        (
            ProducedOutputSemantics.from_existing_main_flow_path(
                producer,
                "A01_s001_w1_z001_t001.tif",
                SourceSchemaFilenameParser(),
            ),
            ProducedOutputSemantics.from_output(
                producer,
                "/memory/other/A01_s001_w1_z001_t001.tif",
                FunctionOutputIdentity(
                    component_values={
                        "well": "A01",
                        "site": 2,
                        "channel": 1,
                        "z_index": 1,
                        "timepoint": 1,
                    },
                    extension=".tif",
                    source="test",
                ),
            ),
        ),
    )

    class RejectImageCache:
        def get(self, *_args, **_kwargs):
            pytest.fail("Ambiguous producer admission must precede cached pixels")

    context = SimpleNamespace(
        microscope_handler=SimpleNamespace(parser=SourceSchemaFilenameParser()),
        runtime_image_stack_cache=RejectImageCache(),
    )
    runtime = function_runtime.PatternGroupExecutionRequest(
        context=context,
        execution_plan=plan,
        compiled_group=plan.compiled_function_pattern.default_group,
        pattern_group_info="A01_s001_w1_z001_t001.tif",
        component_index=0,
        component_count=1,
    )
    monkeypatch.setattr(
        function_runtime, "step_output_manifest", lambda _context: manifest
    )
    monkeypatch.setattr(
        type(runtime),
        "source_workspace_projection_authority",
        lambda _request, *args, **kwargs: (
            lambda: SimpleNamespace(
                projection_if_available=lambda: None,
            )
        )(*args, **kwargs),
    )

    with pytest.raises(NoStepOutputManifestMatch, match="found 2"):
        runtime.load_input_stack()


def test_whole_volume_checkpoint_load_preserves_depth_and_independent_buffers():
    from openhcs.core.aligned_image_payload import ImagePayloadStackComposition
    from openhcs.core.runtime_image_values import image_payload_mask
    from openhcs.core.source_spatial_domain import VolumeSourceSpatialDomain

    pixels = np.arange(3 * 4 * 5, dtype=np.float32).reshape(3, 4, 5)
    mask = pixels % 2 == 0
    metadata = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_spatial_domain=VolumeSourceSpatialDomain(source_depth=3),
    )
    source = metadata.payload_with(pixels, mask)
    plan = CompiledStepPlan(
        step_index=0,
        step_name="Volume",
        step_type="FunctionStep",
        axis_id="A01",
        step_scope_id="volume",
        input_memory_type="numpy",
    )
    loaded = ImagePayloadStackComposition.from_loaded_images(
        (source,),
        producer_records=None,
        execution_plan=plan,
        source_projection=None,
        workspace_source_lookups=(),
    )
    assert image_payload_data(loaded).shape == pixels.shape
    assert loaded.metadata.source_spatial_domain.source_depth == 3
    assert not np.shares_memory(image_payload_data(loaded), pixels)
    assert not np.shares_memory(image_payload_mask(loaded), mask)
    pixels[:] = -1
    mask[:] = False
    assert np.all(image_payload_data(loaded) >= 0)
    assert np.any(image_payload_mask(loaded))
