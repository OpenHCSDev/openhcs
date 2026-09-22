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
import threading
from collections.abc import Mapping
from pathlib import Path
from typing import Optional

import numpy as np
from polystore.filemanager import FileManager

from openhcs.core.streaming_config_declarations import ViewerType
from openhcs.core.streaming_config_factory import (
    StreamingViewerRuntimeConfig,
    ViewerProcessLaunchConfig,
)
from openhcs.runtime.viewer_protocol import (
    DetachedViewerPythonArguments,
    DetachedViewerPythonExpression,
    DetachedViewerServerEntrypointSpec,
    ManagedViewerLifecycleMixin,
    OpenHCSViewerControlMessageType,
    ViewerControlField,
    ViewerControlMessageRequest,
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
    viewer_type=ViewerType.NAPARI,
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
        )

    def existing_viewer_matches_process_launch(self) -> bool:
        """Require exact process-global settings before reusing a viewer."""

        try:
            response = ViewerControlMessageRequest(
                endpoint=self.runtime_endpoint,
                message_type=(OpenHCSViewerControlMessageType.PROCESS_LAUNCH.value),
            ).send()
            if not response.succeeded():
                return False
            wire_config = response.payload[ViewerControlField.PROCESS_LAUNCH.value]
            if not isinstance(wire_config, Mapping):
                raise TypeError(
                    "Napari process-launch response must contain a mapping."
                )
            active_config = ViewerProcessLaunchConfig.from_wire_mapping(wire_config)
        except Exception as error:
            logger.warning(
                "Napari viewer process-launch compatibility check failed: %s",
                error,
            )
            return False
        return active_config == self.process_launch

    def start_viewer(self, async_mode: bool = True):
        """
        Starts the Napari viewer in a separate process.

        Args:
            async_mode: If True, start viewer asynchronously in background thread.
                       If False, wait for viewer to be ready before returning.
        """
        if async_mode:
            # Start viewer asynchronously in background thread
            thread = threading.Thread(target=self._start_viewer_sync, daemon=True)
            thread.start()
            logger.info(
                f"🔬 VISUALIZER: Starting napari viewer asynchronously on port {self.required_port}"
            )
        else:
            # Legacy synchronous mode
            self._start_viewer_sync()

    def _start_viewer_sync(self):
        """Internal synchronous viewer startup (called by start_viewer)."""
        with self._lock:
            port = self.required_port
            self.prepare_fresh_viewer_start()

            if self.lifecycle_state.is_active:
                logger.warning("Napari viewer is already running.")
                return

            # Port is already set in __init__
            logger.info(f"🔬 VISUALIZER: Starting napari viewer process on port {port}")

            # ALL viewers (persistent and non-persistent) should be detached subprocess
            # so they don't block parent process exit. The difference is only whether
            # we terminate them during cleanup.
            logger.info(
                f"🔬 VISUALIZER: Creating {self.persistence_label} napari viewer (detached)"
            )
            self.process = self.launch_detached_viewer()

            process_alive = self.owned_viewer_process_is_alive()

            if process_alive:
                self.lifecycle_state.mark_owned_process()
                logger.info(
                    f"🔬 VISUALIZER: Napari viewer process started successfully (PID: {self.process_pid_label})"
                )
            else:
                logger.error("🔬 VISUALIZER: Failed to start napari viewer process")

    def send_image_data(
        self, step_id: str, image_data: np.ndarray, axis_id: str = "unknown"
    ):
        """
        DISABLED: This method bypasses component-aware stacking.
        All visualization must go through the streaming backend.
        """
        raise RuntimeError(
            f"send_image_data() is disabled. Use streaming backend for component-aware display. "
            f"step_id: {step_id}, axis_id: {axis_id}, shape: {image_data.shape}"
        )

    def stop_viewer(self):
        """Stop the napari viewer process (only if not persistent)."""
        with self._lock:
            if not self.persistent:
                logger.info("🔬 VISUALIZER: Stopping non-persistent napari viewer")
                if self.process:
                    killed = self.terminate_owned_viewer_process()
                    if killed:
                        logger.warning(
                            "🔬 VISUALIZER: Force killing napari viewer process"
                        )
                self.lifecycle_state.mark_stopped()
            else:
                logger.info("🔬 VISUALIZER: Keeping persistent napari viewer alive")
                # DON'T set is_running = False for persistent viewers!
                # The process is still alive and should be reusable

    def visualize_path(
        self, step_id: str, path: str, backend: str, axis_id: Optional[str] = None
    ):
        """
        DISABLED: This method bypasses component-aware stacking.
        All visualization must go through the streaming backend.
        """
        raise RuntimeError(
            f"visualize_path() is disabled. Use streaming backend for component-aware display. "
            f"Path: {path}, step_id: {step_id}, axis_id: {axis_id}"
        )

    def stop(self, timeout: float = 5.0):
        self.stop_viewer()
