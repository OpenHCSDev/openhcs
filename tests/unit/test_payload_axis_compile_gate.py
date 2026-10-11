from pathlib import Path
from types import SimpleNamespace

import numpy as np
import pytest
import tifffile
from polystore.base import ensure_storage_registry, storage_registry
from polystore.filemanager import FileManager
from polystore.virtual_workspace import SourcePixelRef

from openhcs.core.callable_contract import (
    CallableContract,
    PreservedPayloadAxes,
    preserves_payload_axes,
)
from openhcs.core.artifacts import ArtifactSpec, ImageArtifactType
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.component_group_scope import ComponentGroupScope
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.function_patterns import (
    MainFlowInputProjection,
    CompiledFunctionGroup,
    CompiledFunctionInvocation,
    CompiledFunctionPattern,
    FunctionInvocationKey,
    InvocationArtifactInputEdgePlan,
    InvocationArtifactInputProjectionKey,
)
from openhcs.core.pipeline.compilation_session import CompilationSession
from openhcs.core.pipeline.compiler import PipelineCompiler
from openhcs.core.pipeline.function_contracts import artifact_outputs
from openhcs.core.source_bindings import (
    CompiledSourceBindingPlan,
    ComponentSelector,
    NamedSourceBinding,
)
from openhcs.core.source_projection import OpenHCSPlaneAddress, SourcePlaneProjection
from openhcs.core.source_workspace_projection import VirtualWorkspaceSourceProjection
from openhcs.core.step_dependencies import StepInputDependency
from openhcs.processing.backends.cellprofiler.color import color_to_gray
from openhcs.processing.backends.cellprofiler.crop import crop
from openhcs.domains.microscopy.axes import Microscopy


class _CarrierTestSession(SimpleNamespace):
    """Use the production compilation-session ancestry operation in unit tests."""

    def plan(self, index: int) -> CompiledStepPlan:
        return self.plans[index]

    def main_flow_plan_ancestry(
        self,
        index: int,
    ) -> tuple[CompiledStepPlan, ...]:
        return CompilationSession.main_flow_plan_ancestry(self, index)


def _compiled_pattern(
    callable_=color_to_gray, *, input_image_name: str | None = None
) -> CompiledFunctionPattern:
    invocation = CompiledFunctionInvocation(
        key=FunctionInvocationKey(callable_.__name__, "default", 0),
        contract=CallableContract.from_callable(callable_),
    )
    if input_image_name is not None:
        (edge_key,) = InvocationArtifactInputProjectionKey.for_input_count(
            invocation.key, 1
        )
        invocation = invocation.with_artifact_input_edges(
            (
                InvocationArtifactInputEdgePlan(
                    key=edge_key,
                    spec=ArtifactSpec.input(
                        input_image_name, ImageArtifactType, parameter_name="image"
                    ),
                    storage_plan=None,
                    projection=None,
                    main_flow_projection=MainFlowInputProjection.DECLARED_SOURCE_IMAGE,
                ),
            )
        )
    return CompiledFunctionPattern(
        groups=(CompiledFunctionGroup("default", (invocation,)),),
        is_grouped=False,
    )


def test_crop_declares_payload_axis_preservation() -> None:
    assert (
        CallableContract.from_callable(crop).payload_axis_transition
        == PreservedPayloadAxes()
    )


def test_step_input_dependency_owns_ancestry_and_pipeline_start_proofs() -> None:
    pipeline_start = StepInputDependency.pipeline_start()
    step_output = StepInputDependency.step_output(
        source_step_index=3,
        source_step_scope_id="step-3",
    )

    assert pipeline_start.predecessor_step_index() is None
    assert step_output.predecessor_step_index() == 3
    pipeline_start.require_pipeline_start()
    with pytest.raises(ValueError, match="not pipeline-start"):
        step_output.require_pipeline_start()


def _session(
    root: Path,
    paths: tuple[Path, ...],
    *,
    load_as_monochrome: bool = False,
):
    ensure_storage_registry()
    binding = NamedSourceBinding(
        alias="image",
        load_as_monochrome=load_as_monochrome,
    )
    projections = {
        path.name: SourcePlaneProjection(
            address=OpenHCSPlaneAddress(((Microscopy.Well, "A01"), (Microscopy.Site, index), (Microscopy.Channel, 1), (Microscopy.ZIndex, 1), (Microscopy.Timepoint, 1))),
            ref=SourcePixelRef("disk", str(path)),
            source_alias=binding.alias,
        )
        for index, path in enumerate(paths, start=1)
    }
    workspace_projection = VirtualWorkspaceSourceProjection(
        source_refs_by_virtual_path={
            virtual_path: projection.ref
            for virtual_path, projection in projections.items()
        },
        source_metadata_by_path={},
        source_projections_by_virtual_path=projections,
        workspace_root=str(root),
    )
    plan = CompiledStepPlan(
        step_index=0,
        step_name="Convert colour",
        axis_id="A01",
        main_input_dependency=StepInputDependency.pipeline_start(),
        source_binding_plan=CompiledSourceBindingPlan(bindings=(binding,)),
        compiled_function_pattern=_compiled_pattern(),
    )
    context = ProcessingContext(
        step_plans={0: plan},
        axis_id="A01",
        filemanager=FileManager(dict(storage_registry)),
    )
    return _CarrierTestSession(
        plans={0: plan},
        context=context,
        source_workspace_projection=workspace_projection,
    )


def test_mixed_grayscale_and_rgb_sources_fail_compile_before_execution(
    tmp_path: Path,
    monkeypatch,
) -> None:
    grayscale_path = tmp_path / "grayscale.tif"
    rgb_path = tmp_path / "rgb.tif"
    tifffile.imwrite(grayscale_path, np.zeros((8, 9), dtype=np.uint8))
    tifffile.imwrite(
        rgb_path,
        np.zeros((8, 9, 3), dtype=np.uint8),
        photometric="rgb",
    )
    inspected: list[Path] = []
    from openhcs.core.pipeline import compiler as compiler_module

    strict_metadata = compiler_module.require_image_file_source_metadata

    def record_strict_metadata(path: Path):
        inspected.append(path)
        return strict_metadata(path)

    monkeypatch.setattr(
        compiler_module,
        "require_image_file_source_metadata",
        record_strict_metadata,
    )

    with pytest.raises(ValueError, match="failed before execution") as error:
        PipelineCompiler.validate_payload_axis_requirements(
            _session(tmp_path, (grayscale_path, rgb_path))
        )

    assert set(inspected) == {grayscale_path, rgb_path}
    assert str(grayscale_path) in str(error.value)
    assert "ColourAxis" in str(error.value)


def test_all_rgb_sources_prove_color_to_gray_payload_axis_requirement(
    tmp_path: Path,
) -> None:
    paths = (tmp_path / "rgb-1.tif", tmp_path / "rgb-2.tif")
    for path in paths:
        tifffile.imwrite(
            path,
            np.zeros((8, 9, 3), dtype=np.uint8),
            photometric="rgb",
        )

    PipelineCompiler.validate_payload_axis_requirements(
        _session(tmp_path, paths)
    )


def test_grouped_color_requirement_inspects_only_compatible_binding(
    tmp_path: Path,
    monkeypatch,
) -> None:
    grayscale_path = tmp_path / "gray.tif"
    rgb_path = tmp_path / "rgb.tif"
    tifffile.imwrite(grayscale_path, np.zeros((8, 9), dtype=np.uint8))
    tifffile.imwrite(
        rgb_path,
        np.zeros((8, 9, 3), dtype=np.uint8),
        photometric="rgb",
    )
    grayscale_binding = NamedSourceBinding(
        alias="gray",
        component_identity=(ComponentSelector(Microscopy.Channel, "1"),),
    )
    rgb_binding = NamedSourceBinding(
        alias="rgb",
        component_identity=(ComponentSelector(Microscopy.Channel, "2"),),
    )

    def identity(image):
        return image

    color_invocation = CompiledFunctionInvocation(
        key=FunctionInvocationKey("color_to_gray", "2", 0),
        contract=CallableContract.from_callable(color_to_gray),
    )
    gray_invocation = CompiledFunctionInvocation(
        key=FunctionInvocationKey("identity", "1", 0),
        contract=CallableContract.from_callable(identity),
    )
    pattern = CompiledFunctionPattern(
        groups=(
            CompiledFunctionGroup("1", (gray_invocation,)),
            CompiledFunctionGroup("2", (color_invocation,)),
        ),
        is_grouped=True,
    )
    projections = {
        path.name: SourcePlaneProjection(
            address=OpenHCSPlaneAddress(((Microscopy.Well, "A01"), (Microscopy.Site, index), (Microscopy.Channel, binding.component_identity[0].value), (Microscopy.ZIndex, 1), (Microscopy.Timepoint, 1))),
            ref=SourcePixelRef("disk", str(path)),
            source_alias=binding.alias,
        )
        for index, (path, binding) in enumerate(
            (
                (grayscale_path, grayscale_binding),
                (rgb_path, rgb_binding),
            ),
            start=1,
        )
    }
    workspace_projection = VirtualWorkspaceSourceProjection(
        source_refs_by_virtual_path={
            virtual_path: projection.ref
            for virtual_path, projection in projections.items()
        },
        source_metadata_by_path={},
        source_projections_by_virtual_path=projections,
        workspace_root=str(tmp_path),
    )
    plan = CompiledStepPlan(
        step_index=0,
        step_name="Grouped conversion",
        axis_id="A01",
        main_input_dependency=StepInputDependency.pipeline_start(),
        source_binding_plan=CompiledSourceBindingPlan(
            bindings=(grayscale_binding, rgb_binding),
        ),
        execution_group_scope=ComponentGroupScope.from_raw(
            ("1", "2"),
            component=Microscopy.Channel,
        ),
        compiled_function_pattern=pattern,
    )
    ensure_storage_registry()
    context = ProcessingContext(
        step_plans={0: plan},
        axis_id="A01",
        filemanager=FileManager(dict(storage_registry)),
    )
    session = _CarrierTestSession(
        plans={0: plan},
        context=context,
        source_workspace_projection=workspace_projection,
    )
    inspected: list[Path] = []
    from openhcs.core.pipeline import compiler as compiler_module

    strict_metadata = compiler_module.require_image_file_source_metadata

    def record_strict_metadata(path: Path):
        inspected.append(path)
        return strict_metadata(path)

    monkeypatch.setattr(
        compiler_module,
        "require_image_file_source_metadata",
        record_strict_metadata,
    )

    PipelineCompiler.validate_payload_axis_requirements(session)

    assert inspected == [rgb_path]


def test_monochrome_source_binding_removes_required_color_payload_axis(
    tmp_path: Path,
) -> None:
    rgb_path = tmp_path / "rgb.tif"
    tifffile.imwrite(
        rgb_path,
        np.zeros((8, 9, 3), dtype=np.uint8),
        photometric="rgb",
    )

    with pytest.raises(ValueError, match="after source-binding transformations"):
        PipelineCompiler.validate_payload_axis_requirements(
            _session(tmp_path, (rgb_path,), load_as_monochrome=True)
        )


@pytest.mark.parametrize("filename", ("unreadable.tif", "unknown.payload axis"))
def test_unknown_or_unreadable_exact_source_fails_compile_closed(
    tmp_path: Path,
    filename: str,
) -> None:
    path = tmp_path / filename
    path.write_bytes(b"not an image header")

    with pytest.raises(ValueError, match="failed before execution") as error:
        PipelineCompiler.validate_payload_axis_requirements(
            _session(tmp_path, (path,))
        )

    assert str(path) in str(error.value) or str(path.name) in str(error.value)
    assert "ColourAxis" in str(error.value)


def test_declared_preserving_producer_carries_source_proof_between_steps(
    tmp_path: Path,
) -> None:
    rgb_path = tmp_path / "rgb.tif"
    tifffile.imwrite(
        rgb_path,
        np.zeros((8, 9, 3), dtype=np.uint8),
        photometric="rgb",
    )
    session = _session(tmp_path, (rgb_path,))
    binding_plan = session.plans[0].source_binding_plan

    @preserves_payload_axes
    def crop_like(image):
        return image

    producer = CompiledStepPlan(
        step_index=0,
        step_name="Crop",
        axis_id="A01",
        step_scope_id="step-0",
        main_input_dependency=StepInputDependency.pipeline_start(),
        source_binding_plan=binding_plan,
        compiled_function_pattern=_compiled_pattern(crop_like),
    )
    consumer = CompiledStepPlan(
        step_index=1,
        step_name="Convert colour",
        axis_id="A01",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=0,
            source_step_scope_id="step-0",
        ),
        compiled_function_pattern=_compiled_pattern(),
    )
    session.plans = {0: producer, 1: consumer}
    session.context.step_plans = session.plans

    PipelineCompiler.validate_payload_axis_requirements(session)


def test_each_preserving_producer_in_a_chain_carries_source_proof(
    tmp_path: Path,
) -> None:
    rgb_path = tmp_path / "rgb.tif"
    tifffile.imwrite(
        rgb_path,
        np.zeros((8, 9, 3), dtype=np.uint8),
        photometric="rgb",
    )
    session = _session(tmp_path, (rgb_path,))
    binding_plan = session.plans[0].source_binding_plan

    @preserves_payload_axes
    def crop_like(image):
        return image

    first_producer = CompiledStepPlan(
        step_index=0,
        step_name="First crop",
        axis_id="A01",
        step_scope_id="step-0",
        main_input_dependency=StepInputDependency.pipeline_start(),
        source_binding_plan=binding_plan,
        compiled_function_pattern=_compiled_pattern(crop_like),
    )
    second_producer = CompiledStepPlan(
        step_index=1,
        step_name="Second crop",
        axis_id="A01",
        step_scope_id="step-1",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=0,
            source_step_scope_id="step-0",
        ),
        compiled_function_pattern=_compiled_pattern(crop_like),
    )
    consumer = CompiledStepPlan(
        step_index=2,
        step_name="Convert colour",
        axis_id="A01",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=1,
            source_step_scope_id="step-1",
        ),
        compiled_function_pattern=_compiled_pattern(),
    )
    session.plans = {0: first_producer, 1: second_producer, 2: consumer}
    session.context.step_plans = session.plans

    PipelineCompiler.validate_payload_axis_requirements(session)


def test_unproved_producer_transition_fails_compile_closed(tmp_path: Path) -> None:
    rgb_path = tmp_path / "rgb.tif"
    tifffile.imwrite(
        rgb_path,
        np.zeros((8, 9, 3), dtype=np.uint8),
        photometric="rgb",
    )
    session = _session(tmp_path, (rgb_path,))
    binding_plan = session.plans[0].source_binding_plan

    def unknown_transform(image):
        return image

    producer = CompiledStepPlan(
        step_index=0,
        step_name="Unknown transform",
        axis_id="A01",
        step_scope_id="step-0",
        main_input_dependency=StepInputDependency.pipeline_start(),
        source_binding_plan=binding_plan,
        compiled_function_pattern=_compiled_pattern(unknown_transform),
    )
    consumer = CompiledStepPlan(
        step_index=1,
        step_name="Convert colour",
        axis_id="A01",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=0,
            source_step_scope_id="step-0",
        ),
        compiled_function_pattern=_compiled_pattern(),
    )
    session.plans = {0: producer, 1: consumer}
    session.context.step_plans = session.plans

    with pytest.raises(ValueError, match="not preserved.*unknown_transform"):
        PipelineCompiler.validate_payload_axis_requirements(session)


@pytest.mark.parametrize("source_kind", ("rgb", "gray", "missing-anchor"))
def test_inherited_bindings_trace_exact_named_payload_axis_edges(
    tmp_path: Path, source_kind: str
) -> None:
    path = tmp_path / "source.tif"
    if source_kind == "gray":
        tifffile.imwrite(path, np.zeros((8, 9), dtype=np.uint8))
    else:
        tifffile.imwrite(path, np.zeros((8, 9, 3), dtype=np.uint8), photometric="rgb")
    session = _session(tmp_path, (path,))
    bindings = session.plans[0].source_binding_plan

    @preserves_payload_axes
    def crop_like(image):
        return image

    plans = {}
    for index, (callable_, input_name) in enumerate(
        (
            (crop_like, "missing" if source_kind == "missing-anchor" else "image"),
            (crop_like, "FirstCrop"),
            (color_to_gray, "SecondCrop"),
        )
    ):
        plans[index] = CompiledStepPlan(
            step_index=index,
            step_name=f"Carrier step {index}",
            axis_id="A01",
            step_scope_id=f"step-{index}",
            main_input_dependency=(
                StepInputDependency.pipeline_start()
                if index == 0
                else StepInputDependency.step_output(
                    source_step_index=index - 1,
                    source_step_scope_id=f"step-{index - 1}",
                )
            ),
            source_binding_plan=bindings,
            compiled_function_pattern=_compiled_pattern(
                callable_, input_image_name=input_name
            ),
        )
    session.plans = plans
    session.context.step_plans = plans
    if source_kind == "rgb":
        PipelineCompiler.validate_payload_axis_requirements(session)
    else:
        expected = (
            "ColourAxis"
            if source_kind == "gray"
            else "exact primary source-binding projection"
        )
        with pytest.raises(ValueError, match=expected):
            PipelineCompiler.validate_payload_axis_requirements(session)


def test_generic_main_flow_preservation_does_not_prove_payload_axis(
    tmp_path: Path,
) -> None:
    """Artifact-flow preservation is not a payload axis transition declaration."""

    rgb_path = tmp_path / "rgb.tif"
    tifffile.imwrite(
        rgb_path,
        np.zeros((8, 9, 3), dtype=np.uint8),
        photometric="rgb",
    )
    session = _session(tmp_path, (rgb_path,))
    binding_plan = session.plans[0].source_binding_plan

    @artifact_outputs("measurement")
    def generic_flow_preserver(image):
        return image

    generic_contract = CallableContract.from_callable(generic_flow_preserver)
    assert generic_contract.preserves_input_main_flow()
    assert generic_contract.payload_axis_transition is None
    producer = CompiledStepPlan(
        step_index=0,
        step_name="Generic flow producer",
        axis_id="A01",
        step_scope_id="step-0",
        main_input_dependency=StepInputDependency.pipeline_start(),
        source_binding_plan=binding_plan,
        compiled_function_pattern=_compiled_pattern(generic_flow_preserver),
    )
    consumer = CompiledStepPlan(
        step_index=1,
        step_name="Convert colour",
        axis_id="A01",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=0,
            source_step_scope_id="step-0",
        ),
        compiled_function_pattern=_compiled_pattern(),
    )
    session.plans = {0: producer, 1: consumer}
    session.context.step_plans = session.plans

    with pytest.raises(ValueError, match="not preserved.*generic_flow_preserver"):
        PipelineCompiler.validate_payload_axis_requirements(session)


def test_unknown_routed_group_cannot_fall_back_to_all_primary_sources(
    tmp_path: Path,
) -> None:
    """A bad typed group projection must fail instead of broadening evidence."""

    grayscale_path = tmp_path / "gray.tif"
    rgb_path = tmp_path / "rgb.tif"
    tifffile.imwrite(grayscale_path, np.zeros((8, 9), dtype=np.uint8))
    tifffile.imwrite(
        rgb_path,
        np.zeros((8, 9, 3), dtype=np.uint8),
        photometric="rgb",
    )
    grayscale_binding = NamedSourceBinding(
        alias="gray",
        component_identity=(ComponentSelector(Microscopy.Channel, "1"),),
    )
    rgb_binding = NamedSourceBinding(
        alias="rgb",
        component_identity=(ComponentSelector(Microscopy.Channel, "2"),),
    )
    color_invocation = CompiledFunctionInvocation(
        key=FunctionInvocationKey("color_to_gray", "3", 0),
        contract=CallableContract.from_callable(color_to_gray),
    )
    pattern = CompiledFunctionPattern(
        groups=(CompiledFunctionGroup("3", (color_invocation,)),),
        is_grouped=True,
    )
    projections = {
        grayscale_path.name: SourcePlaneProjection(
            address=OpenHCSPlaneAddress(((Microscopy.Well, "A01"), (Microscopy.Site, 1), (Microscopy.Channel, 1), (Microscopy.ZIndex, 1), (Microscopy.Timepoint, 1))),
            ref=SourcePixelRef("disk", str(grayscale_path)),
            source_alias=grayscale_binding.alias,
        ),
        rgb_path.name: SourcePlaneProjection(
            address=OpenHCSPlaneAddress(((Microscopy.Well, "A01"), (Microscopy.Site, 2), (Microscopy.Channel, 2), (Microscopy.ZIndex, 1), (Microscopy.Timepoint, 1))),
            ref=SourcePixelRef("disk", str(rgb_path)),
            source_alias=rgb_binding.alias,
        ),
    }
    workspace_projection = VirtualWorkspaceSourceProjection(
        source_refs_by_virtual_path={
            virtual_path: projection.ref
            for virtual_path, projection in projections.items()
        },
        source_metadata_by_path={},
        source_projections_by_virtual_path=projections,
        workspace_root=str(tmp_path),
    )
    plan = CompiledStepPlan(
        step_index=0,
        step_name="Unknown routed conversion",
        axis_id="A01",
        main_input_dependency=StepInputDependency.pipeline_start(),
        source_binding_plan=CompiledSourceBindingPlan(
            bindings=(grayscale_binding, rgb_binding),
        ),
        execution_group_scope=ComponentGroupScope.from_raw(
            ("1", "2"),
            component=Microscopy.Channel,
        ),
        compiled_function_pattern=pattern,
    )
    ensure_storage_registry()
    session = _CarrierTestSession(
        plans={0: plan},
        context=ProcessingContext(
            step_plans={0: plan},
            axis_id="A01",
            filemanager=FileManager(dict(storage_registry)),
        ),
        source_workspace_projection=workspace_projection,
    )

    with pytest.raises(ValueError, match="cannot project source bindings"):
        PipelineCompiler.validate_payload_axis_requirements(session)
