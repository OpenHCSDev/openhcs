Explicit Centrosome watershed: current-main integration
=======================================================

Owner and scope
---------------

PR227's engineering owner is Zeno; the OpenHCS issue-batch parent owns this
integration checkpoint. Zeno's original tree is unchanged. Review continues
in ``/home/ts/wt/openhcs-centrosome-integration-20260930``, branch
``integrate/centrosome-registration-20260930``, associated with existing PR227,
not a competing implementation PR.

Original PR head ``aebaa2686d9799f4383ea4e26e14992c85bcc612`` normally merges
main ``c50f42c46fcee71c88bc5883850b1001bc00f212`` as
``6f1628e5b4fab04a3e18c027cc7256d09676c5c9``. The production difference remains
the original ten-line backend declaration/export. No numerical procedure,
selector, registry, configuration, default, native C++ source or caller changes.
Two new cases exercise the actual primary-object callable. Old tests remain
unchanged. Existing declarations own memory/provider identity and lookup;
the new member inherits the original Python request/heap implementation.
This follows IMPL-4/MEMB-1 without a consumer switch or parallel roster.

Persisted formats: none changed. Registered user processing function names,
PipelineDocument, configuration fields and numerical/result formats unchanged.
The already-public CENTROSOME provider gains its missing watershed member;
the existing Numba default and unsupported-selection errors are retained.

Actual source checks
--------------------

Six provider-family cases passed, no skips/deselections, 3.19 seconds;
process 3.69 seconds, exit 0, 20-second shell bound. Two warnings concern the
deliberately unloaded asyncio plugin, not behavior failures.
Junit evidence is retained outside the implementation tree at
``/home/ts/wt/openhcs-issue-batch-20260929/centrosome-primary-source-tests-20260930.xml``.

The original four cases cover signed-marker labels, forbidden production
centrosome dependency imports, masked plane/volume connectivity, default
selection and fail-closed unsupported providers/memory. Two new cases run
identify_primary_objects on an independently generated 24-by-32, two-peak
float32 image, with explicit Centrosome morphology and, respectively,
CENTROSOME/NATIVE watershed. The real threshold, declumping, request,
signed-marker watershed, relabeling, typed label and measurement paths execute.
Only request observation wraps the real validated_request method; computation
is not mocked. Checks require the selected provider, signed seeds -2/-1,
int32 labels 0/1/2, exact foreground mask, explicit semantic object IDs 1/2,
one threshold-measurement row and unchanged returned/original image.

The first exploratory callable command on the old branch failed at its known
``_granularity_reconstruct`` import before computation. Normal main integration
brings the already-merged ABI/module fix; no workaround was added to production.
The first integrated exploratory command reached the correct labels but
incorrectly demanded directly stored ``declared_object_ids``. The actual domain
owner legitimately declares contiguous IDs through ``declared_object_count``.
The behavioral test uses that owner's ``require_explicit_id_domain`` contract
and still requires exactly 1/2. No existing assertion was weakened or deleted.

Runtime provenance and boundedness
---------------------------------

Existing Python ``/home/ts/code/projects/openhcs/.venv/bin/python`` only.
PYTHONPATH gives reviewed source priority, followed by the eight existing
submodule src paths at ``openhcs-custom-function-admission-20260929``.
Those dependency gitlinks equal the integrated source's recorded gitlinks.
OpenHCS import location is asserted inside the new integration tree;
ZMQRuntime, PolyStore, metaclass-registry and python-introspect imports are
asserted inside the shared existing dependency tree. No submodule/env download.

The two existing ``_tabular_native.abi3.so`` and ``_granularity_native.abi3.so``
extensions are loaded under their original qualified module names from the
installed source using importlib's extension loader. Their C++ and setup sources
are unchanged between installed ``295e0ee`` and the integrated source. No copied
binary, Python replacement, build, installation or production import path edit.

Thread limits are one; bytecode, pytest cache, optional plugin loading and fixture
capture are disabled. ``NUMBA_DISABLE_JIT=1`` makes this a bounded source-body
check, not a compiled-kernel acceptance claim. The newly selected watershed
member itself intentionally uses the original Python reference path. No actual
native runtime, MCP/GUI/viewer, JVM, provider, frozen science or reference-answer
data was opened. All inputs are generated inside the test.

Remaining acceptance
--------------------

The source journey is a shippable review checkpoint, not proof of independent
CellProfiler oracle parity, compiled-kernel parity, fresh installed callable
readiness, real compile/execute or biological acceptance. Those remain open on
issue226/PR227 and must not be represented as completed. Hosted CI is not the
reason to defer those checks. Resource guard is critical at swap 16.3 GiB;
no new heavy/native or blind allocation is admitted. Original H001 failure,
H003 frozen result and held-out/reference boundaries remain unchanged.
