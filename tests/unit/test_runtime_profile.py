"""Bound runtime emitters preserve the shared sink's gating and output effects."""

import logging
import builtins
from concurrent.futures import ThreadPoolExecutor
from threading import Barrier

import pytest

from openhcs.core.runtime_profile import (
    PROFILE_RUNTIME_ENV,
    PROFILE_RUNTIME_PATH_ENV,
    RuntimeProfiler,
    RuntimeProfileLogger,
)


def test_bound_profiler_disabled_has_no_output_effects(monkeypatch, tmp_path, caplog):
    path = tmp_path / "profile.log"
    monkeypatch.setenv(PROFILE_RUNTIME_ENV, "false")
    monkeypatch.setenv(PROFILE_RUNTIME_PATH_ENV, str(path))
    profiler = RuntimeProfiler(logging.getLogger("test.bound.runtime.disabled"))

    with caplog.at_level(logging.INFO):
        with RuntimeProfileLogger.run():
            profiler.log("phase", 0.125, objects=3)

    assert not profiler.enabled()
    assert not path.exists()
    assert not caplog.records


def test_bound_profiler_buffers_without_io_then_flushes_once(
    monkeypatch, tmp_path, caplog
):
    path = tmp_path / "profile.log"
    monkeypatch.setenv(PROFILE_RUNTIME_ENV, "TRUE")
    monkeypatch.setenv(PROFILE_RUNTIME_PATH_ENV, str(path))
    profiler = RuntimeProfiler(logging.getLogger("test.bound.runtime.enabled"))
    writes = []
    original_open = builtins.open

    def track_open(*args, **kwargs):
        writes.append(args[0])
        return original_open(*args, **kwargs)

    monkeypatch.setattr(builtins, "open", track_open)
    metadata = {"CHANNEL": 2}

    with caplog.at_level(logging.INFO):
        with RuntimeProfileLogger.run():
            profiler.log("phase", 0.125, objects=3, source="nuclei")
            profiler.log("metadata", 0.25, components=metadata)
            metadata["CHANNEL"] = 7
            assert not path.exists()
            assert not caplog.records
            assert not writes

    assert profiler.enabled()
    expected = "RUNTIME_PROFILE phase 0.125000s objects=3 source=nuclei"
    second = "RUNTIME_PROFILE metadata 0.250000s components={'CHANNEL': 2}"
    assert path.read_text() == expected + "\n" + second + "\n"
    assert [record.getMessage() for record in caplog.records][:2] == [expected, second]
    assert len(writes) == 1


def test_profile_error_flush_keeps_original_failure_and_next_run_clean(
    monkeypatch, tmp_path
):
    path = tmp_path / "profile.log"
    monkeypatch.setenv(PROFILE_RUNTIME_ENV, "true")
    monkeypatch.setenv(PROFILE_RUNTIME_PATH_ENV, str(path))
    profiler = RuntimeProfiler(logging.getLogger("test.runtime.failure"))
    from openhcs.core.orchestrator.cancellation import ExecutionCancelledError

    with pytest.raises(ExecutionCancelledError, match="cancelled"):
        with RuntimeProfileLogger.run(execution_id="cancelled"):
            profiler.log("before_cancel", 0.5)
            raise ExecutionCancelledError("cancelled")
    profiler.log("out_of_run", 1.0)
    with RuntimeProfileLogger.run(execution_id="next"):
        profiler.log("next", 0.125)
    lines = path.read_text().splitlines()
    assert len(lines) == 2
    assert "before_cancel" in lines[0] and "execution_id=cancelled" in lines[0]
    assert "execution_id=next" in lines[1] and "out_of_run" not in path.read_text()


def test_profile_runs_remain_independent_in_concurrent_worker_threads(
    monkeypatch, tmp_path
):
    monkeypatch.setenv(PROFILE_RUNTIME_ENV, "true")
    path = tmp_path / "profile.log"
    monkeypatch.setenv(PROFILE_RUNTIME_PATH_ENV, str(path))
    barrier = Barrier(2)
    profiler = RuntimeProfiler(logging.getLogger("test.runtime.concurrent"))

    def worker(name):
        with RuntimeProfileLogger.run(execution_id=name):
            profiler.log("first", 0.1, owner=name)
            barrier.wait()
            profiler.log("last", 0.2, owner=name)

    with ThreadPoolExecutor(max_workers=2) as executor:
        tuple(executor.map(worker, ("left", "right")))
    lines = path.read_text().splitlines()
    assert len(lines) == 4
    for name in ("left", "right"):
        owned = [line for line in lines if f"execution_id={name}" in line]
        assert len(owned) == 2 and all(f"owner={name}" in line for line in owned)


@pytest.mark.parametrize("sparse", [False, True])
def test_cellprofiler_label_profile_preserves_storage_geometry(
    monkeypatch, tmp_path, sparse
):
    import numpy as np
    from openhcs.core.runtime_object_labels import (
        ObjectLabelPayload, ObjectLabelVariantData, ObjectLabelRepresentation,
        SparseIJVObjectLabelStorageStrategy,
    )
    from openhcs.core.runtime_sparse_labels import SparseIJVLabelRows
    from openhcs.interop.cellprofiler.runtime.profile_fields import (
        cellprofiler_profile_payload_fields, object_label_artifact_profile_fields,
    )
    from openhcs.interop.cellprofiler.runtime.runtime_profile import (
        CellProfilerRuntimeProfileLogger,
    )

    # The same pixel belongs to two objects: profiling must preserve the IJV
    # representation, rather than collapse it into a dense segmentation.
    data = (
        SparseIJVLabelRows(np.array([[0, 1, 1], [0, 1, 2]], dtype=np.int32))
        if sparse else np.array([[0, 1], [2, 0]], dtype=np.int32)
    )
    labels = ObjectLabelPayload(
        variant_data=ObjectLabelVariantData(labels=data),
        representation=(ObjectLabelRepresentation.SPARSE_IJV if sparse
                        else ObjectLabelRepresentation.DENSE_LABELS),
    )
    def reject_dense(*args, **kwargs):
        raise AssertionError("Profiling must not densify sparse labels")
    monkeypatch.setattr(SparseIJVObjectLabelStorageStrategy, "dense_data", reject_dense)
    expected_shape = None if sparse else (2, 2)
    assert object_label_artifact_profile_fields(labels)["label_shape"] == expected_shape
    payload_fields = cellprofiler_profile_payload_fields("value", labels)
    assert payload_fields["value_shape"] == expected_shape
    assert payload_fields["value_nbytes"] == (None if sparse else 16)
    path = tmp_path / "labels.log"
    monkeypatch.setenv(PROFILE_RUNTIME_ENV, "true")
    monkeypatch.setenv(PROFILE_RUNTIME_PATH_ENV, str(path))
    with RuntimeProfileLogger.run():
        CellProfilerRuntimeProfileLogger.object_label_artifact(
            "labels", 0.1, artifact_name="Objects", payload_type="labels", labels=labels,
        )
    assert f"label_shape={expected_shape}" in path.read_text()
    assert labels.labels is data
    if sparse:
        np.testing.assert_array_equal(data.as_array(), [[0, 1, 1], [0, 1, 2]])


def test_cellprofiler_disabled_label_profile_does_not_build_fields(monkeypatch):
    from openhcs.interop.cellprofiler.runtime import runtime_profile

    monkeypatch.setenv(PROFILE_RUNTIME_ENV, "false")
    def reject_fields(value):
        raise AssertionError("Disabled profiling must not inspect labels")
    monkeypatch.setattr(runtime_profile, "object_label_artifact_profile_fields", reject_fields)
    runtime_profile.CellProfilerRuntimeProfileLogger.object_label_artifact(
        "labels", 0.1, artifact_name="Objects", payload_type="labels", labels=object(),
    )


def test_cellprofiler_lazy_label_profile_uses_held_geometry(monkeypatch):
    import numpy as np
    from openhcs.core.runtime_object_labels import (
        ObjectLabelPayload, ObjectLabelVariantData, PlaneStackObjectLabelVariantData,
    )
    from openhcs.interop.cellprofiler.runtime.profile_fields import (
        cellprofiler_profile_payload_fields, object_label_artifact_profile_fields,
    )

    variants = PlaneStackObjectLabelVariantData(
        [ObjectLabelVariantData(np.ones((2, 3), dtype=np.int32)),
         ObjectLabelVariantData(np.ones((2, 3), dtype=np.int32))],
        "numpy",
    )
    labels = ObjectLabelPayload(variant_data=variants)
    def reject_dense(*args, **kwargs):
        raise AssertionError("Profiling must not assemble lazy label planes")
    monkeypatch.setattr(PlaneStackObjectLabelVariantData, "_dense_variant", reject_dense)
    assert object_label_artifact_profile_fields(labels)["label_shape"] == (2, 2, 3)
    fields = cellprofiler_profile_payload_fields("value", labels)
    assert fields["value_shape"] == (2, 2, 3)
    assert fields["value_nbytes"] == 48
    assert not variants._dense_variants
