"""Compiler persistence follows declared versus compiler-added export ownership."""

from types import SimpleNamespace

from openhcs.core.pipeline.artifact_planning import TerminalMaterializationSpec
from openhcs.core.pipeline.compiler import PipelineCompiler
from openhcs.core.pipeline.materialization_flag_planner import (
    MaterializationFlagPlanner,
)
from openhcs.processing.materialization import (
    ImageFileOptions,
    MaterializationSpec,
    ROIOptions,
)


def test_disabling_automatic_materialization_keeps_only_declared_exports(
    monkeypatch,
) -> None:
    backend_requests = []

    def backend(context, vfs_config):
        backend_requests.append((context, vfs_config))
        return "disk"

    monkeypatch.setattr(
        MaterializationFlagPlanner,
        "_resolve_materialization_backend",
        staticmethod(backend),
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
    vfs_config = object()
    session = SimpleNamespace(
        global_config=SimpleNamespace(
            materialize_runtime_artifacts=False,
            vfs_config=vfs_config,
        ),
        context=context,
        plans=plans,
    )

    PipelineCompiler._compile_runtime_artifact_materialization_plans(session)

    assert backend_requests == [(context, vfs_config)]
    assert not plans[0].runtime_artifact_materialization.has_persistent_target
    assert plans[1].runtime_artifact_materialization.has_persistent_target
    assert plans[1].runtime_artifact_materialization.require_persistent_backend() == (
        "disk"
    )
