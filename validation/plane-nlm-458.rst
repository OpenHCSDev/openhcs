Explicit independent-plane CPU NLM: source checkpoint
===================================================

Issue #458; Dewey implementation, parent installed integration, Planck frozen
science input and synthetic fixture. Base main
``17c6306069cf89ea39cc349be69c38843628152e``. Finished checkout reused after
clean status, .pth borrower and /proc reference checks. Published 456 branch
and all original failure evidence remain intact. Resource helper returned
critical disk headroom (home 4.7 GiB); only small serial source work is admitted.
No environment, backing package, native process or scientific input changes.

Owner trace before edit
-----------------------

Original NRA ``PythonEnumBaseAuthority`` and refactor-audit ``measure_source``
read all Python sources under the actual import roots, followed by semantic
reading of the relevant declarations, inheritance, writes, checks, imports and
call consumers. No parser failures:

* Own OpenHCS production: 703 modules, 5194 classes, 436 direct enum declarations,
  10109 imports, 58375 writes, 36602 decisions/comparisons.
* Paired installed arraybridge: 17 modules, 29 classes, 3 enums.
* BasicPy backing python_introspect: 12 modules, 48 classes.
* Paired installed metaclass_registry: 6 modules, 14 classes, 1 enum.
* Actual backing scikit-image: 355 modules, 82 classes (includes installed tests).

Exact roots:
``/home/ts/wt/openhcs-paired-raw-installed-parent-20261001/.venv/lib/python3.12/site-packages/{arraybridge,metaclass_registry}``,
``/home/ts/wt/basicpy-live-candidate-20260930/.venv/lib/python3.12/site-packages/python_introspect``,
``/home/ts/code/projects/openhcs/.venv/lib/python3.12/site-packages/skimage``.
Own OpenHCS root is this checkout's ``openhcs``. AST inheritance recognition is
source-level, not dynamic metaclass membership or alias resolution; Cython and
binary allocations, ContextVar projection and live registry discovery are not
static proofs. This is not a complete NRA FULL/R1 proof or scientific result.

The family consumer search covered ProcessingContract, PURE_2D slicers and
aggregators, memory decorators, arraybridge SliceBySliceRuntimeParameter,
CallableContract, function_patterns, CP function/module execution, pipeline
authoring, parameter documentation, canonical registry, source serialization,
and all native JAX/Torch/CellProfiler NLM declarations. Existing PURE_2D and its
nominal payload strategies own the full slice/project/execute/restack mechanism.
FLEXIBLE composes stack requirement and PURE_2D behavior through real existing
MI. No alternative slicer, control roster, registry or library implementation
is introduced. New declaration chooses the existing contract at its owning
NumPy processor surface; the external original kernel remains the sole NLM
algorithm. No ornamental inheritance is needed.

Applicable catalog entries: MEMB-2 declaration-derived capabilities; IMPL-1/2/5
avoid consumer mode/name dispatch; IMPL-12 avoid copied kernel/slicing procedure;
BOUND-1 keep input interpretation at its declared boundary. Explicit 2-D raw ABI
rejection is not permission to infer a missing axis. Original volumetric
scikit-image callable and defaults are untouched. Unknown kwargs and hidden
runtime control admission are not broadened.

Focused source and live qualification
------------------------------------

Production checkpoint ``c7820b50ed19ef647dba961d1db9addfd19731e5`` changes only
``openhcs/processing/backends/processors/numpy_processor.py``. The registry's
original local declaration projection produces the public function ID
``openhcs:processors_numpy_processor_non_local_means_denoise_planes``. The
original nominal transport resolves that same declaration without preparing a
second catalog. Public kwargs validation admits the original NLM parameters and
rejects ``channel_axis``, ``slice_by_slice``, ``plane_axis`` and unknown kwargs.

``validation/plane-nlm-source03.log.gz``: 26 PASS, 7.155 seconds,
450124 KiB aggregate RSS, one CPU, 512 MiB/60 seconds. Twelve new source cases
and fourteen unchanged unified-registry/payload controls. The new family cases
call the actual installed scikit-image kernel, both fast/slow paths, on one or
three explicitly declared planes. Each raw NLM call receives float32[16,20],
1280 input bytes; all output values equal independent original 2-D calls,
shape/dtype, input immutability, plane axis, exact provenance, source names,
spatial domain and declared physical spacing are checked. No synthetic test
calibration is assigned to biological data.

Volumetric control uses the original scikit-image library adapter and FLEXIBLE
wrapper, not a replacement algorithm: the real fast 3-D kernel receives
[3,16,20,1], including scikit-image's appended channel singleton. All three
spatial axes remain, and output equals the original volumetric call. Bare
singleton stacks, volumes and color ndarrays are explicitly rejected by the
new plane-only raw ABI rather than squeezed or inferred.

New-case proof adds one independent PURE_2D declaration and executes it through
the unchanged catalog/wrapper/projection/restack consumers. A separate original
FLEXIBLE declaration exercises its existing multiple-inheritance behavior with
``slice_by_slice=True`` and ``False``: raw calls receive three 2-D planes or
one full volume respectively. No generic consumer, enum member roster or MRO
switch was added. Shared mechanisms and their original cooperative payload
aggregation remain unchanged. This extends declarations, not a compatibility
alias, forwarding facade or replacement library implementation.

Original source attempts are retained, not overwritten:

* source01: 6 FAIL/5 PASS, 7.405 seconds, 453956 KiB. The fixture omitted each
  provenance plane's declared C1 alias, which the original projection correctly
  added. Its hand-built volume spy bypassed the real library adapter and leaked
  the semantic control into scikit-image. Corrected fixture declares the alias
  on its original provenance owner; corrected control uses the original adapter.
* source02: 3 FAIL/9 PASS, 6.752 seconds, 450540 KiB. Source names used a scalar
  alias instead of explicit per-plane aliases and were expanded by original
  restacking. The volume oracle omitted scikit-image's appended channel axis.
  Source03 declares complete plane names and checks the actual original ABI.
  Exact identity/value/rank assertions remain; no production compatibility
  reader, shape cast or assertion skip was introduced.

``validation/plane-nlm-owner-closure.log.gz`` records before/after full Python
roots, also adding the actual ObjectState .pth backing resolved by find_spec:
``/home/ts/wt/basicpy-live-candidate-20260930/.venv/lib/python3.12/site-packages/objectstate``
(27 modules). Both snapshots parse 1120 modules with zero omissions. Direct
enums/classes are unchanged. The sole production delta is the new NumPy
declaration: no catalog/registry, slicing, metadata, runtime or library copies.
Closure itself completes in 41.313 seconds, 155008 KiB, the same bounded scope.
AST parse/dynamic-resolution limits above still apply. This is not global R1.

Original pinned R0 ``validation/plane-nlm-pinned-r0.log.gz``: PASS, zero positive
deltas, 14.205 seconds, 162612 KiB aggregate RSS. Exact unchanged tool
agent-comms ``3b03785f45df2ef5dc62ba6aed99294192ecbb01`` via the original retained
Git importer, actual Python3.14 and readonly BasicPy metaclass backing. Comparison
is base main17c630 to productionc7820b, scope ``openhcs``. Later changes are
tests/docs only. Ruff F and diff whitespace checks pass. Full NRA R1/FULL is
not rerun under source512MiB/60s; previous global budget failures remain separate.

Original checkpoint TIFF header was read without reading scientific pixels:
one float32[2586,2586] page, 10032669 bytes. That persisted storage rank does
not prove the original runtime NLM input rank, intermediate buffers or OOM cause.

Parent-installed MCP/native synthetic compile/execute and peak/rank/provenance
proof are pending. No native or viewer is launched by this worker. Planck's
frozen science and parent integration ownership remain unchanged. Source tests
do not qualify ONE08 or a candidate09 biological analysis.

Original ONE08 isolated OOM, incomplete job status and missing actual kernel
rank remain unmodified in the parent evidence root. This route is not an OOM
guarantee for arbitrary plane size and is not a validated biological parameter
choice. Root394 owns any subsequent runtime/core correction.

Normal main integration checkpoint
----------------------------------

After the 26-case source checkpoint, current PR394 was checked at
``01875a7724532932787efa7522b5da0406fae321``. Its roster includes the shared
CallableContract, unified registry and CP smoothing owners, but does not include
``processors/numpy_processor.py``. None of those shared files was edited.
Main ``cc9fcdfd4eb87feac96759bfc18ff174763d2677`` (merged parent-qualified454)
was fetched and merged normally into this retained branch. New declaration
bytes and its 26-case tested sources are unchanged; production comparison to
that main remains solely the original54-line NumPy addition. No qualified
source shard or R0 is rerun for this integration. Parent's ordinary wheel and
small public installed/native qualification are distinct ongoing work; this
worker does not launch them or touch any live scientific environment.

Finite installed engineering handoff
------------------------------------

Parent/Planck can use a NEW small singleton-SITE synthetic fixture, never the
original ONE08 input, on the parent's separately admitted serialized slot:

1. Search/describe the canonical function ID above in the installed catalog.
   Its contract must be PURE_2D and typed NLM parameter values must be exposed.
2. Public create/add/validate/render using the fixture's original enabled exact
   source bindings and actual declared calibration/provenance. Use small
   engineering-only patch_size3/patch_distance2/h0.075/fast_modeTrue/sigma0/
   preserve_rangeTrue, not a guessed scientific candidate. The function has no
   channel_axis or slice control: grayscale-plane semantics belong to its
   declaration. Keep the exact clean rendered source for artifact plan and
   source-session creation, then native compile and execute once.
3. Input is known 64x64 float32 with original singleton SITE assembly. The
   registered function must succeed while its original raw ABI rejects rank
   other than2; source controls separately measured actual kernel entry rank
   and bytes. If live entry rank/buffer bytes are only inferred from this guard,
   label that inference rather than claiming a new live telemetry observation.
4. Read the compiled main-flow output slot, not an unrelated artifact/viewer
   layer. Compare all4096 persisted values to one independent original 2-D NLM
   reference with identical kwargs; check64x64/dtype, exact source identity,
   physical channel, unit/spacing, declared axes and source metadata unchanged.
   Preserve original request/reply journals, native completion, aggregate peak
   and exact lifecycle disposition. Retain every failure/UNKNOWN without replay.
5. A tiny actual-Z volumetric control must still use the original external NLM,
   not the independent-plane declaration. Independent planes intentionally
   exclude cross-plane neighbors even when the declared plane axis is true Z.

The original PublicJourney/dev-client journal and request-token machinery can
be reused by the integration owner. No second harness/poller/runtime/cache or
dependency download is needed. Native acceptance is not silently substituted
by the source checks. Original #458 remains open until this finite live scope
is qualified. No disposable source test directory was created (the tests did
not need pytest tmp_path); removed0 bytes, no cleanup performed.
