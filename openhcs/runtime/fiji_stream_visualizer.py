"""
Fiji stream visualizer for OpenHCS.

Manages Fiji viewer instances for real-time visualization via ZMQ.
Uses FijiViewerServer (inherits from ZMQServer) for PyImageJ-based display.
Follows same architecture as NapariStreamVisualizer.
"""

from __future__ import annotations

import logging
from pathlib import Path

from polystore.filemanager import FileManager

from openhcs.core.streaming_config_declarations import FijiViewer
from openhcs.core.streaming_config_factory import StreamingViewerRuntimeConfig
from openhcs.runtime.viewer_protocol import (
    DetachedViewerPythonArguments,
    DetachedViewerPythonExpression,
    DetachedViewerServerEntrypointSpec,
    ManagedViewerLifecycleMixin,
)

logger = logging.getLogger(__name__)

FIJI_VIEWER_ENTRYPOINT = DetachedViewerServerEntrypointSpec(
    viewer_family=FijiViewer,
    module_name="openhcs.runtime.fiji_viewer_server",
    function_name="fiji_viewer_server_process",
    extra_imports=("from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG",),
)


class FijiStreamVisualizer(ManagedViewerLifecycleMixin):
    """
    Manages Fiji viewer instance for real-time visualization via ZMQ.

    Follows same architecture as NapariStreamVisualizer.
    """

    viewer_process_label = "Fiji"
    detached_server_entrypoint = FIJI_VIEWER_ENTRYPOINT

    def __init__(
        self,
        *,
        filemanager: FileManager,
        runtime_config: StreamingViewerRuntimeConfig,
    ):
        super().__init__(runtime_config=runtime_config)
        self.filemanager = filemanager

    def detached_server_arguments(
        self,
        *,
        log_file: Path,
    ) -> DetachedViewerPythonArguments:
        return DetachedViewerPythonArguments.from_literals(
            self.required_port,
            self.viewer_title,
            None,
            str(log_file),
            self.display_enabled,
        ).append(
            DetachedViewerPythonExpression.symbol("transport_mode"),
            DetachedViewerPythonExpression.symbol("OPENHCS_ZMQ_CONFIG"),
            DetachedViewerPythonExpression.literal(self.process_launch.listen_host),
        )
