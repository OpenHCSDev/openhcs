Batch Workflow Service
======================

Module
------

``openhcs.pyqt_gui.widgets.shared.services.batch_workflow_service``

Purpose
-------

``BatchWorkflowService`` is the single orchestration boundary for:

- compile-only batches
- execute batches (compile-all first, execute-all after)
- execution completion polling
- progress projection refresh + server-status emission

Core Types
----------

- ``CompileJob``: immutable compile unit
- ``BatchWorkflowService``: end-to-end compile/execute owner

Dependency Boundary
-------------------

OpenHCS workflow policy is implemented in ``BatchWorkflowService``. Runtime and
UI polling primitives are consumed as dependencies:

- ``BatchSubmitWaitEngine`` (from ``zmqruntime.execution``)
- ``ExecutionStatusPoller`` (from ``zmqruntime.execution``)
- ``IntervalSnapshotPoller`` (from ``pyqt_reactive.services``)

OpenHCS docs define orchestration policy and host contracts only; generic
engine internals are documented in their owning repositories.

Flow: Compile Only
------------------

1. Reset progress views for new batch.
2. Build ``CompileJob`` entries from selected plates.
3. Submit all jobs then wait all jobs via ``BatchSubmitWaitEngine``.
4. Write compiled data into ``host.plate_compiled_data``.
5. Emit orchestrator state transitions and progress updates.

Flow: Run Batch
---------------

1. Reset progress and execution state.
2. Mark all selected plates queued immediately.
3. Compile all selected plates before any execution submission.
4. Submit execution for each plate using ``compile_artifact_id``.
5. Start per-execution completion pollers.
6. Converge to completed/failed/cancelled through one callback path.

Host Contract (Expected Attributes/Callbacks)
---------------------------------------------

``BatchWorkflowService`` expects host-owned UI/state callbacks including:

- ``emit_status``, ``emit_error``, ``emit_progress_*``
- ``update_item_list``, ``update_button_states``
- ``emit_orchestrator_state``, ``emit_execution_complete``
- ``on_plate_completed``, ``on_all_plates_completed``
- data stores like ``plate_compiled_data``, ``plate_execution_states``,
  ``plate_execution_ids``, and ``_progress_tracker``

This is an explicit nominal integration in OpenHCS (not runtime duck-typing).

Related Modules
---------------

- ``openhcs.pyqt_gui.widgets.shared.services.execution_server_status_presenter``
- ``openhcs.pyqt_gui.widgets.shared.services.progress_batch_reset``
- ``openhcs.pyqt_gui.widgets.shared.services.plate_config_resolver``
- ``openhcs.pyqt_gui.widgets.shared.services.zmq_client_service``

See Also
--------

- :doc:`plate_manager_services`
- :doc:`progress_runtime_projection_system`
- :doc:`zmq_server_browser_system`
