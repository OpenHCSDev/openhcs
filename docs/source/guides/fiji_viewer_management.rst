Fiji streaming
==============

Fiji streaming uses the same compiled streaming boundary as Napari, with an
OpenHCS Fiji adapter and a detached Fiji/ImageJ viewer process.

Setup
-----

Install ``openhcs[gui,fiji]`` or ``openhcs[gui,viz]`` and verify that the
PyImageJ/Java environment can start independently. In the Pipeline Editor,
enable the Fiji streaming configuration for the step and compile before
running.

PolyStore's ``FIJI_IMAGEJ_RUNTIME`` declaration owns the Fiji endpoint and
managed Java compatibility requirement. OpenHCS initializes Fiji through that
declaration before any JVM starts in the detached viewer process. Do not start
another JVM in that process or duplicate its Java constraint in application
configuration.

OpenHCS compiles component order and display metadata into the stream plan. The
viewer adapter constructs ImageJ-compatible displays from the typed payload; a
pipeline declaration does not launch Fiji directly and should not embed a ZMQ
port or hand-built wire message.

Lifecycle
---------

ZMQRuntime owns generic readiness checks, control messages, acknowledgments, and
process management. OpenHCS owns the Fiji entry point, ImageJ conversion, macro
integration, and viewer-specific presentation. PolyStore owns selection of the
compatible ImageJ runtime and controlled gateway/JVM shutdown. The OpenHCS
server delegates that shutdown after stopping its ZMQ transport, so Python
interpreter finalization is not a second resource-lifecycle authority.
Persistent viewers may be reused only after the control protocol confirms that
the bound process is compatible.

Settlement and inspection boundary
----------------------------------

Fiji answers the same typed ``SETTLE`` control as Napari through the shared
viewer control actions. Its display path batches streamed items through
PolyStore's debounced batch engine, and ``SETTLE`` reports
``ViewerSettleProgress`` for the queued and active batches: running until every
queued item has rendered, complete afterwards, or failed with the retained
native rendering error. Fiji has no queue of deferred Qt layer-route updates;
the two viewers share the settlement contract, not an internal update model.

Fiji does **not** currently provide Napari-style live viewer-state or payload
projection. It registers no ``STATE`` or ``PAYLOADS`` control action, so those
requests return an explicit unsupported-control error. Inspection clients
therefore cannot query Fiji layers, axes, labels, payload arrays, or payload
summaries through those controls. This is a declared capability boundary, not a
port/readiness failure; do not retry it as transport recovery or infer viewer
state from window titles.

Fiji macro execution, display construction, readiness, clear-state control, and
process lifecycle remain separate supported surfaces. Use Napari when automated
post-render layer/payload evidence is required.

For shared behavior, see :doc:`viewer_management` and
:doc:`../architecture/streaming_boundary_and_wrappers`.
