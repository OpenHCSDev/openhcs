"""Exact deletion gates for persistent-only artifact materialization."""

from __future__ import annotations

import inspect
from pathlib import Path

import numpy as np
import pytest
from polystore.base import DataSink
from polystore.config import TiffCompression, TiffConfig
from polystore.streaming.identity import StreamProducerIdentity

from openhcs.core.steps.function_artifact_materialization import (
    ArtifactMaterializationTargetPlan,
    PersistentArtifactMaterializationTargetPlan,
    RuntimeArtifactMaterialization,
)
from openhcs.core.artifacts import ArtifactOutputPlan, ImageArtifactType
from openhcs.core.runtime_artifact_values import RuntimeValue
from openhcs.core.runtime_stores import RuntimeValueStore
from openhcs.processing.materialization.core import (
    MaterializationSpec,
    Output,
    RawBackendKwargs,
)
from openhcs.processing.materialization.options import ImageFileOptions


class _PersistentBackend(DataSink):
    requires_filesystem_validation = False

    def contextual_save_kwargs(self, *, images_dir: str) -> dict[str, object]:
        del images_dir
        return {}

    def supports_file_path(self, path: str) -> bool:
        del path
        return False

    def save(self, data, identifier, **kwargs):
        raise AssertionError("This projection test must not save")

    def save_batch(self, data_list, identifiers, **kwargs):
        raise AssertionError("This projection test must not save")


def test_persistent_tiff_kwargs_apply_only_to_tiff_outputs() -> None:
    config = TiffConfig(compression=TiffCompression.DEFLATE)
    kwargs = RawBackendKwargs(tiff_config=config)
    outputs = (
        Output(path="/results/summary.csv", content="well,count\nA01,1\n"),
        Output(path="/results/labels.tif", content=np.zeros((8, 8), dtype=np.int32)),
        Output(path="/results/labels2.tiff", content=np.zeros((8, 8), dtype=np.int32)),
    )

    batches = kwargs.filemanager_batches(outputs)

    assert tuple(output.path for output in batches[0][0]) == ("/results/summary.csv",)
    assert batches[0][1] == {}
    assert tuple(output.path for output in batches[1][0]) == (
        "/results/labels.tif",
        "/results/labels2.tiff",
    )
    assert batches[1][1] == {"tiff_config": config}


class _FileManager:
    def __init__(self) -> None:
        self.backend = _PersistentBackend()

    def _get_backend(self, backend: str) -> _PersistentBackend:
        del backend
        return self.backend


@pytest.mark.parametrize(
    ("payload", "streaming_viewer_surfaces"),
    (
        (np.empty((0, 4, 4), dtype=np.uint16), {}),
        (np.ones((60, 4, 4), dtype=np.uint16), {"viewer": object()}),
    ),
)
def test_persistent_only_backend_kwargs_skip_stream_payload_projection(
    monkeypatch: pytest.MonkeyPatch,
    payload: np.ndarray,
    streaming_viewer_surfaces: dict[str, object],
) -> None:
    def unexpected_stream_metadata(*_args: object, **_kwargs: object) -> None:
        raise AssertionError(
            "persistent-only materialization projected stream metadata"
        )

    monkeypatch.setattr(
        RuntimeArtifactMaterialization,
        "stream_source_metadata_items",
        unexpected_stream_metadata,
    )
    spec = MaterializationSpec(ImageFileOptions(filename_suffix=".tif"))
    output_plan = ArtifactOutputPlan(
        name="SavedImage",
        path="/memory/SavedImage.pkl",
        artifact_type=ImageArtifactType,
        materialization=spec,
    )
    record = RuntimeValueStore().record(
        RuntimeValue.normalize(output_plan, payload, axis_id="A01"),
        path=output_plan.path,
        backend="memory",
    )
    materialization = RuntimeArtifactMaterialization(
        output_plan=output_plan,
        spec=spec,
        record=record,
        data=payload,
        base_path=Path("/images/SavedImage.tif"),
        source_identity=None,
        filename_source_identity=None,
    )
    target = PersistentArtifactMaterializationTargetPlan("disk")
    kwargs = target.backend_kwargs(
        materialization=materialization,
        persistent_backend_kwargs={"disk": RawBackendKwargs()},
        streaming_viewer_surfaces=streaming_viewer_surfaces,
        fallback_source_identity=None,
        producer_identity=StreamProducerIdentity(
            origin="pipeline",
            output_kind="artifact",
            output_key="SavedImage",
            projection_key="SavedImage",
        ),
        context=object(),
        filemanager=_FileManager(),
        images_dir="/images",
        stream_output_paths=("/images/SavedImage.tif",),
    )

    assert tuple(kwargs) == ("disk",)
    assert dict(kwargs["disk"]) == {}


def test_backend_kwargs_no_longer_accepts_eager_stream_metadata() -> None:
    assert (
        "source_metadata_items"
        not in inspect.signature(
            ArtifactMaterializationTargetPlan.backend_kwargs
        ).parameters
    )
