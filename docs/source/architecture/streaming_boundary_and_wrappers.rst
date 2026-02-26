Streaming Boundary And Wrappers
===============================

Overview
--------

OpenHCS now treats streaming as a thin-wrapper integration surface, not as the
owner of generic streaming infrastructure.

Ownership
---------

- ``zmqruntime`` owns transport and execution lifecycle primitives:
  ZMQ sockets, control/data channels, ping/pong, execution status contracts.
- ``polystore`` owns streaming payload semantics and receiver-side projection:
  streaming data types, component-mode grouping, batching/debounce engines, and
  viewer receiver helpers.
- ``openhcs`` owns application wiring:
  configuration defaults, orchestrator integration, and OpenHCS-specific viewer
  process launch/lifecycle policy.

Current OpenHCS Responsibility
------------------------------

In OpenHCS runtime modules (for example ``openhcs/runtime/fiji_viewer_server.py``
and ``openhcs/runtime/napari_*``), the server classes should remain thin
wrappers that bind OpenHCS configuration/context into external abstractions.

They should not re-implement generic projection or batching logic that is
already provided by ``polystore`` receiver-core modules.

Why This Split
--------------

- keeps OpenHCS focused on domain orchestration and UX integration
- improves reuse for other applications that need the same streaming stack
- reduces duplicated logic and inconsistent behavior across viewers
- gives one canonical path per semantic concept

