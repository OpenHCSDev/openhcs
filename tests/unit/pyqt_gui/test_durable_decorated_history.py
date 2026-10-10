"""Continuous native declaration/history restart with a retained runtime wrapper.

This exercises the real document and ObjectState owners, without a GUI or data
execution. Live desktop capture/restore remains a separate acceptance boundary.
"""

import threading
from pathlib import Path

import numpy as np
from arraybridge.decorators import ThreadGPUContext
from arraybridge.types import MemoryType
from objectstate import ObjectStateRegistry
from pyqt_reactive.services.scope_token_service import ScopeTokenService

from openhcs.core.config import PipelineConfig
from openhcs.core.memory import numpy
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.processors.numpy_processor import tophat
from openhcs.pyqt_gui.services.pipeline_object_state_binding import (
    PipelineObjectStateBinding,
)

SCOPE = "/isolated/durable-decorated-history"


def test_declarations_and_retained_callable_history_survive_native_restart(
    tmp_path: Path,
):
    ObjectStateRegistry.clear()
    ScopeTokenService.clear_scope(SCOPE)
    runtime = ThreadGPUContext.current()
    runtime_key = (MemoryType.CUPY, -2)
    runtime_handle = threading.local()
    runtime._streams[runtime_key] = runtime_handle
    try:
        # An old callable no longer exported by its original package is retained
        # by undo. Its wrapper's globals own thread-local GPU context storage.
        @numpy
        def old(image, scale=3):
            return image * scale

        with ObjectStateRegistry.atomic("retained custom declaration"):
            PipelineObjectStateBinding.update_plate_steps(
                SCOPE, [FunctionStep(name="old custom", func=(old, {"scale": 7}))]
            )
            PipelineObjectStateBinding.commit_plate_state(SCOPE)
        baseline_id = ObjectStateRegistry.get_branch_history()[-1].id
        expected_baseline = PipelineObjectStateBinding.steps_for_plate(SCOPE)[0]
        with ObjectStateRegistry.atomic("current native declaration"):
            PipelineObjectStateBinding.update_plate_steps(
                SCOPE,
                [FunctionStep(name="current", func=(tophat, {"selem_radius": 17}))],
            )
            PipelineObjectStateBinding.commit_plate_state(SCOPE)
        head_id = ObjectStateRegistry.get_branch_history()[-1].id
        expected_current = PipelineObjectStateBinding.steps_for_plate(SCOPE)[0]
        snapshot_ids = tuple(s.id for s in ObjectStateRegistry.get_branch_history())
        source = PipelineDocumentCodec.render(
            PipelineDocumentCodec.from_values(
                pipeline_config=PipelineConfig(),
                pipeline_steps=PipelineObjectStateBinding.steps_for_plate(SCOPE),
            )
        )
        declarations = tmp_path / "current.py"
        declarations.write_text(source)
        history = tmp_path / "history.objectstate"
        ObjectStateRegistry.save_history_to_file(str(history))

        ObjectStateRegistry.clear()
        ScopeTokenService.clear_scope(SCOPE)
        parsed = PipelineDocumentCodec.from_source(declarations.read_text())
        PipelineObjectStateBinding.update_plate_steps(SCOPE, parsed.pipeline_steps)
        ObjectStateRegistry.load_history_from_file(str(history))
        assert (
            tuple(s.id for s in ObjectStateRegistry.get_branch_history())
            == snapshot_ids
        )
        current = PipelineObjectStateBinding.steps_for_plate(SCOPE)[0]
        assert current.name == "current"
        assert current.func == expected_current.func
        assert ObjectStateRegistry.time_travel_to_snapshot(baseline_id)
        restored = PipelineObjectStateBinding.steps_for_plate(SCOPE)[0]
        historical, kwargs = restored.func
        assert restored.name == "old custom"
        assert kwargs == expected_baseline.func[1]
        np.testing.assert_array_equal(
            historical(np.array([1, 2], dtype=np.uint16), **kwargs), [7, 14]
        )
        assert ObjectStateRegistry.time_travel_to_snapshot(head_id)
        assert PipelineObjectStateBinding.steps_for_plate(SCOPE)[0].func == current.func
        assert ThreadGPUContext.current() is runtime
        assert runtime._streams[runtime_key] is runtime_handle
    finally:
        runtime._streams.pop(runtime_key, None)
        ObjectStateRegistry.clear()
        ScopeTokenService.clear_scope(SCOPE)
