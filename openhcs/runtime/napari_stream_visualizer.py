"""
Napari-based real-time visualization module for OpenHCS.

This module provides the NapariStreamVisualizer class for real-time
visualization of tensors during pipeline execution.

Doctrinal Clauses:
- Clause 65 — No Fallback Logic
- Clause 66 — Immutability After Construction
- Clause 88 — No Inferred Capabilities
- Clause 368 — Visualization Must Be Observer-Only
"""

from __future__ import annotations

import logging
from pathlib import Path

from polystore.filemanager import FileManager

from openhcs.core.streaming_config_declarations import NapariViewer
from openhcs.core.streaming_config_factory import (
    StreamingViewerRuntimeConfig,
)
from openhcs.runtime.viewer_protocol import (
    DetachedViewerPythonArguments,
    DetachedViewerPythonExpression,
    DetachedViewerServerEntrypointSpec,
    ManagedViewerLifecycleMixin,
)
from openhcs.utils.import_utils import optional_import_or_none

# Optional napari import - this module should only be imported if napari is available
napari = optional_import_or_none("napari")
if napari is None:
    raise ImportError(
        "napari is required for NapariStreamVisualizer. "
        "Install it with: pip install 'openhcs[viz]' or pip install napari"
    )


logger = logging.getLogger(__name__)

NAPARI_VIEWER_ENTRYPOINT = DetachedViewerServerEntrypointSpec(
    viewer_family=NapariViewer,
    module_name="openhcs.runtime.napari_viewer_server",
    function_name="run_napari_viewer_process",
)


class NapariStreamVisualizer(ManagedViewerLifecycleMixin):
    """
    Manages a Napari viewer instance for real-time visualization of tensors
    streamed from the OpenHCS pipeline. Runs napari in a separate process
    for Qt compatibility and true persistence across pipeline runs.
    """

    viewer_process_label = "Napari"
    detached_server_entrypoint = NAPARI_VIEWER_ENTRYPOINT
    starts_in_background = True

    def __init__(
        self,
        *,
        filemanager: FileManager,
        runtime_config: StreamingViewerRuntimeConfig,
        replace_layers: bool = False,
    ):
        super().__init__(runtime_config=runtime_config)
        self.filemanager = filemanager
        self.replace_layers = replace_layers

        # Clause 368: Visualization must be observer-only.
        # This class will only read data and display it.

    def detached_server_arguments(
        self,
        *,
        log_file: Path,
    ) -> DetachedViewerPythonArguments:
        return DetachedViewerPythonArguments.from_literals(
            self.required_port,
            self.viewer_title,
            self.replace_layers,
            str(log_file),
        ).append(
            DetachedViewerPythonExpression.symbol("transport_mode"),
            DetachedViewerPythonExpression.literal(self.scope_accent_color),
            DetachedViewerPythonExpression.literal(self.process_launch.qt_font_dpi),
            DetachedViewerPythonExpression.literal(self.process_launch.listen_host),
        )

