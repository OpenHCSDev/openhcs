ZMQ execution transition
========================

ZMQRuntime owns generic transport; OpenHCS owns its compiled-execution adapter.
The generic ``EndpointApplication`` declaration owns exact expected-versus-
observed compatibility, and the connection retains the readiness
``PongResponse`` carrying the observed identity. OpenHCS supplies one versioned
application declaration for execution and UI endpoints. The UI observes the
resulting compatibility value and may request a state-preserving endpoint and
desktop restart. No second probe, copied version field, or UI-owned connection
flag participates in the decision.

Each ``EndpointConnectionAttempt`` executes under one cancellation authority,
either allocated by the attempt or supplied by its caller. Cancelling that
authority raises ``EndpointConnectionCancelledError`` and disconnects a
connection that won a late readiness race. The endpoint function-catalogue
service supplies its request cancellation to the connection attempt as well,
so GUI teardown covers endpoint-lock waiting, process startup, readiness, and
catalogue polling without a second flag or timeout. OpenHCS can therefore
accept teardown during endpoint startup without treating it as a server
failure or matching text.

``TransportEndpoint`` also owns the configured data/control port pair and the
exact subset currently occupied. Proof-gated stale cleanup and forced local
release descend through the selected transport declaration as well. Launchers
and test harnesses use that typed endpoint authority instead of duplicating the
control-port offset, reconstructing a pair, or branching on transport mode.
Every transport declaration also projects its endpoint-specific startup-lock
path. ZMQRuntime acquires that lock across processes under the caller's shared
cancellation token and operation deadline, so concurrent desktop and MCP
clients cannot both launch a server for the same endpoint.

ZMQRuntime also owns the execution status transition boundary. Terminal states
are immutable, a cancellation request addresses one execution, and queued
cancellation does not interrupt an unrelated running execution. OpenHCS extends
the generic interruption hook with its exact orchestrator and worker ownership;
inline and threaded work then stops at the next cooperative boundary.

OpenHCS execution submission reuses ZMQRuntime's monotonic
``OperationDeadline`` across endpoint startup, progress registration, task
serialisation, and the execute request. ``OpenHCSZMQConfig`` owns this dedicated
submission budget separately from the shorter budget for status, stop, and
other control requests. Startup activity may refresh the endpoint inactivity
deadline, but it cannot extend the caller's total submit budget. OpenHCS reports
separately whether preparation expired before the execute request or the
request was sent without a reply, so callers do not invent an execution
identifier or retry an unknown outcome blindly.

An accepted headless job retains the exact client that submitted it. Status
polling reuses that client, projects its ZMQRuntime-owned latest progress
observation, and disconnects it after caching a terminal response. It does not
recreate clients for polling or mirror transport progress in an OpenHCS-owned
registry. The job also retains the exact typed submission and accepting endpoint
handshake. A successful completion projects those facts with the server's typed
execution record, including its results and timing boundaries, so evidence
writers need not reconstruct the pipeline or parse a separate status source.

The ordinary ZMQ client checks the endpoint's OpenHCS application compatibility
before sending any compile or execution request. Benchmark callers use that same
admission method; they do not maintain a separate version rule.

The headless cancellation capability addresses that retained client's exact
job identifier. Its service delegates the bounded request to the ordinary
execution client and returns the server's applied flag with the observed job
status; a client timeout alone is not treated as successful cancellation.
Optional runtime-observation export follows the same submission path: the
agent path policy validates the destination, and the client/server shared
auxiliary declaration carries it and its typed value-or-outcome scope to the
existing execution server. Outcome-only export does not require runtime array
values to return to the parent when the compiled plan does not need them. It
retains file-export paths from the same compiled output contexts as a full
observation, without collecting intermediate runtime records. The
benchmark layer need not submit a second kind of job to collect that evidence.
Both export scopes carry the producing server execution ID, and the ordinary
export writer will not replace an existing file. The benchmark finaliser
checks that ID against the completed ordinary job before retaining its receipt.
The current value and outcome exports also compare execution-result membership
with the compiled axis set; a successful subset cannot become a completed
measurement merely because its reported axes succeeded.
The server-owned observation also carries a startup snapshot of its Python
interpreter and installed distribution versions. Benchmark receipts project
that observation without treating the client environment as the server's.
The snapshot does not establish the environment of a remote worker.
The ordinary compiled-run result also projects the server's completion summary
and typed output-plate metadata; benchmark adapters consume those projections
instead of decoding transport response keys themselves.

A source-backed execution session may retain an original ``plate_path`` while
declaring a different prepared ``execution_plate_path``. The shared ZMQ
execution identity selects the prepared path when present, independently of a
selected external pipeline file. The pycodified ``pipeline_source`` remains
the pipeline authority; a second selected-pipeline path is rejected for that
session. Both paths pass the ordinary agent read-path policy before submission.

The execution server owns one ``FunctionCatalogPreparation``. On a cold cache,
``RegistryService`` launches the launcher's dedicated
``--prepare-capabilities`` mode as an isolated child so behaviour probing runs
on that interpreter's main thread without recursively constructing another
execution server. The server projects preparation snapshots while clients
poll, and its shutdown cancels the shared ``OperationCancellation``, stops the
exact child if it is still alive, and joins the preparation thread before
backend cleanup. Both the preparation child and a newly spawned execution
server receive the environment projected by ArrayBridge's ``MemoryType``
declarations. The same declaration-owned framework requirements therefore
govern parent admission, catalogue preparation, and server startup; OpenHCS
does not rebuild NVIDIA wheel paths in either launcher.

The execution client starts its server from the OpenHCS data directory rather
than inheriting an arbitrary caller working directory. The shared OpenHCS log
path declaration owns both the server log and its startup journal. A successful
readiness handshake removes the journal; a failed startup retains it beside the
log so the last reported phase remains available for diagnosis.

``RegistryService`` admits an optional backend only after that backend's own
registry declaration proves its runtime warm-up and complete module inventory.
The admitted inventory remains fixed for the interpreter lifetime and is reused
on both sides of persistent-cache preparation. A partially installed optional
runtime therefore stays absent instead of reappearing after a failed import and
invalidating an otherwise usable catalogue.

For native callables, local nominal declarations own any catalogue-module
projection. Only declarations on that module's public surface enter the
browsable catalogue; an explicitly transported private decorated callable can
still be reconstructed from its own contract. Cache identity includes the
current source revision and framework admission context. Distinct admission
contexts, such as CPU-only and GPU-capable sessions, own distinct persistent
cache documents and therefore cannot replace one another during concurrent
preparation. A failed projection publishes no partial catalogue, and PolyStore's
atomic JSON writer replaces one cache as a complete document. A reader that
encounters an older or invalid document leaves the path intact while fresh
preparation publishes its replacement. Clearing the service removes every
derived lookup view. The transport service therefore consumes one
declaration-derived catalogue instead of synchronizing a second function
registry.

Catalogue control messages preserve the endpoint's complete membership revision
across full and filtered pages. Detail reads and callable-reference reads require
that revision, and a reference contains the registry-owned canonical key and
processing contract. Desktop and local MCP consumers can therefore resolve one
selected callable without importing every catalogue member or reclassifying its
semantics locally.

Batch shutdown is likewise bound to the exact typed endpoint, including its host
and transport. Cleanup cannot reinterpret a non-default TCP endpoint through a
local transport default.

See :doc:`external_foundations`.
