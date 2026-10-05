"""Compiler persistence follows declared versus compiler-added export ownership."""

from pathlib import Path
from types import SimpleNamespace

import pytest

from openhcs.core.compiled_step_plan import RuntimeArtifactMaterializationPlan
from openhcs.core.pipeline.compiler import PipelineCompiler
from openhcs.core.pipeline.materialization_flag_planner import (
    MaterializationFlagPlanner,
)
from openhcs.processing.materialization import (
    ImageFileOptions,
    MaterializationSpec,
    ROIOptions,
)
from openhcs.processing.materialization.persistence import TerminalMaterializationSpec


def test_disabling_automatic_materialization_keeps_only_declared_exports(
    monkeypatch,
) -> None:
    backend_requests = []

    def backend(self, declaration):
        backend_requests.append(declaration)
        return "disk"

    monkeypatch.setattr(
        MaterializationFlagPlanner,
        "resolve_backend",
        backend,
    )
    automatic_labels = SimpleNamespace(
        materialization=TerminalMaterializationSpec(ROIOptions(min_area=1))
    )
    declared_image = SimpleNamespace(
        materialization=MaterializationSpec(ImageFileOptions())
    )
    plans = {
        0: SimpleNamespace(artifact_outputs={"labels": automatic_labels}),
        1: SimpleNamespace(artifact_outputs={"export": declared_image}),
    }
    context = object()
    vfs_config = SimpleNamespace(materialization_backend="disk")
    session = SimpleNamespace(
        global_config=SimpleNamespace(
            materialize_runtime_artifacts=False,
            vfs_config=vfs_config,
        ),
        context=context,
        plans=plans,
    )

    planner = MaterializationFlagPlanner(
        pipeline_config=SimpleNamespace(
            path_planning_config=SimpleNamespace(well_filter=None)
        ),
        microscope_handler=SimpleNamespace(),
        filemanager=object(),
        input_dir=Path("/plate"),
        available_axis_values=("A01",),
    )
    PipelineCompiler._compile_runtime_artifact_materialization_plans(session, planner)

    assert backend_requests == [vfs_config.materialization_backend]
    assert not plans[0].runtime_artifact_materialization.has_persistent_target
    assert plans[1].runtime_artifact_materialization.has_persistent_target
    assert plans[1].runtime_artifact_materialization.require_persistent_backend() == (
        "disk"
    )


@pytest.mark.parametrize("backend", ("disk", "memory", "new-persistent-backend"))
def test_materialization_owner_admits_only_its_enabled_backend(backend):
    disabled = RuntimeArtifactMaterializationPlan.disabled()
    enabled = RuntimeArtifactMaterializationPlan(
        persistent_enabled=True, persistent_backend=backend
    )
    assert disabled.persists_to_backend(backend) is False
    assert enabled.persists_to_backend(backend) is True
    assert enabled.persists_to_backend("other-backend") is False
    with pytest.raises(RuntimeError, match="has no persistent backend"):
        RuntimeArtifactMaterializationPlan(persistent_enabled=True).persists_to_backend(
            backend
        )
