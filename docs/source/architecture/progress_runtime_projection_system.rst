Progress Runtime Projection System
==================================

Scope
-----

This page documents the OpenHCS implementation path only.

The generic progress abstraction lives in ``zmqruntime.progress`` and is
documented in the ``zmqruntime`` docs.

OpenHCS Implementation Path
---------------------------

OpenHCS-specific modules:

- ``openhcs.core.progress.types`` (domain event vocabulary + semantics)
- ``openhcs.core.progress.registry`` (OpenHCS semantic keying wrapper)
- ``openhcs.core.progress.projection`` (OpenHCS adapter + runtime projection API)
- ``openhcs.core.progress.emitters`` (orchestrator/step event emission)

Consumption path:

1. Emit typed ``ProgressEvent`` values from compile/execute flows.
2. Route events through explicit queue wiring via ``set_progress_queue(...)``.
3. Register events in ``ProgressRegistry`` with semantic channel keying.
4. Build runtime projection for UI status derivation.
5. Render projection in plate manager and ZMQ server browser services.

OpenHCS Invariants
------------------

- Canonical execution tree path is ``plate -> worker -> well -> step``.
- ``PATTERN_GROUP`` is step-detail only and does not set well pipeline percent.
- Plate/server status is derived from projection snapshots, not mutable cache.

Canonical Abstraction Docs
--------------------------

See ``zmqruntime`` for abstraction internals:

- ``external/zmqruntime/docs/source/architecture/progress_registry_projection.rst``
- ``external/zmqruntime/docs/source/architecture/zmq_execution_system.rst``

Related OpenHCS Pages
---------------------

- :doc:`batch_workflow_service`
- :doc:`zmq_server_browser_system`
