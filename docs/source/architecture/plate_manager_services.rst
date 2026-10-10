The OpenHCS session
===================

Every client of OpenHCS (the Qt GUI, headless MCP, scripts) works through one
``Session`` (``openhcs/authoring/session``). The session holds no copy of what
ObjectState already owns: the dataset list, each dataset's ``PipelineConfig``
and its pipeline steps live in ObjectState. The session owns the runtime state
around them: pending initialisation and compilation, compiled artifacts, the
execution batch, debug sessions, live measurements and the runtime projection.

Ownership map
-------------

``session.py``
  ``Session``: dataset add/delete/split, initialisation, compile and run, stop,
  debug runs, finished-execution records, admission checks, and the ports a
  client supplies (``MainThread``, ``DatasetAccess``, ``Renderer``).

``operations/``
  The ``SessionOperation`` family. One class per action: label, tooltip,
  request and result types, availability and ``run``. Headless operations are
  also MCP tools, derived in ``openhcs.agent.capabilities``; renderer
  operations ask the attached renderer to present something.

``views.py``
  ``SessionView`` family: ``DatasetListView`` and ``PipelineStepsView`` derive
  frozen states (``openhcs.agent.dto.session``) and name the operations a
  renderer binds to its buttons.

``events.py``
  The ``SessionEvent`` family and the event log. Clients subscribe (the GUI's
  ``QtSessionEventRelay``) or wait for events past a sequence number (MCP's
  ``openhcs_session_events``); none polls.

``compile_batch.py``, ``submission.py``, ``execution_control.py``, ``debug_runs.py``, ``progress.py``
  Compile batches, submission and terminal following, stop and failure
  convergence, debug execution, progress registration and projection.

``dataset_document.py``
  The datasets as one code document: render it, and apply an edited one within
  a selected or all-datasets ``DatasetDocumentScope``.

``pipelines.py``
  Pipeline declaration reconciliation and saved-baseline commits for the
  pipeline, step and nested-function ObjectState graph.

Dataset scope kinds (``core/dataset_sources/dataset_scopes.py``) say what a row
stands for; CellProfiler registers one row per ``.cppipe`` from interop.
Pipeline file formats are ``PipelineImporter`` subclasses keyed by suffix.

Invariants
----------

- Every selected run compiles before the first execution submission, and each
  execution carries the compile artifact id returned for its dataset.
- Initialisation and compilation reserve the affected dataset before
  asynchronous work; execution reserves the batch before connecting.
- A selected code document preserves every unselected dataset and rejects a
  payload whose scope ids differ from the ones it was read with.
- Session work that touches ObjectState runs on the client's main thread
  (``DispatcherThread`` over the Qt dispatcher in the GUI and in MCP).
- Widgets hold no session state; they render views and invoke operations.

See :doc:`batch_workflow_service`, :doc:`progress_runtime_projection_system`,
and :doc:`zmq_server_browser_system`.
