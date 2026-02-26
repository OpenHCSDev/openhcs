PlateManager Services Architecture
==================================

The Problem: Parallel Service Paths Drifted
-------------------------------------------

The previous PlateManager architecture split orchestration across independent
``CompilationService`` and ``ZMQExecutionService`` modules. That split caused
state duplication and stale UI projections because compile and execute flows
could diverge in how they updated plate state, progress, and status strings.

Current Service Model
---------------------

PlateManager now uses a unified service boundary:

- ``BatchWorkflowService`` for compile + execute orchestration
- ``ExecutionServerStatusPresenter`` for consistent status-line rendering
- ``progress_batch_reset`` for deterministic batch boundary resets
- ``plate_config_resolver`` for canonical per-plate pipeline config lookup

This service layer keeps the widget focused on UI state and delegates workflow
policy to reusable service classes.

Canonical Workflow
------------------

Compile-only flow:

1. Build ``CompileJob`` objects from selected plates.
2. Submit all compile jobs through the workflow service compile backend.
3. Wait all compile jobs.
4. Store compiled artifacts and mark orchestrator states.

Run flow:

1. Reset progress for a new batch.
2. Compile all selected plates first.
3. Submit all execution jobs with compile artifact IDs.
4. Poll completion per execution and converge states in one place.

Key Invariants
--------------

- One service owns compile + run orchestration.
- Batch reset always clears old progress before new work starts.
- Plate list state is updated from a single source (workflow service callbacks).
- Progress projection and server status text are derived data, not mutable cache.

Primary Modules
---------------

- ``openhcs/pyqt_gui/widgets/shared/services/batch_workflow_service.py``
- ``openhcs/pyqt_gui/widgets/shared/services/execution_server_status_presenter.py``
- ``openhcs/pyqt_gui/widgets/shared/services/progress_batch_reset.py``
- ``openhcs/pyqt_gui/widgets/shared/services/plate_config_resolver.py``

Related Architecture Pages
--------------------------

- :doc:`batch_workflow_service`
- :doc:`progress_runtime_projection_system`
- :doc:`zmq_server_browser_system`
