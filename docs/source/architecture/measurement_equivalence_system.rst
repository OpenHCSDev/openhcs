Measurement and runtime equivalence
===================================

Runtime equivalence compares semantic outputs rather than requiring byte-for-byte
identity. It is used to validate backend and CellProfiler parity while accounting
for measurement dialects, row identity, object-label domains, relationships, and
declared numeric tolerances.

Inputs
------

Equivalence operates on runtime observations and snapshots built from typed
artifacts:

- images and masks
- measurement tables and columnar rows
- object labels and object-instance catalogs
- directed object relationships
- spatial grids and sparse label rows

Artifact names, types, execution scopes, source provenance, and component groups
remain part of the comparison identity.

Measurement identity
--------------------

``RuntimeMeasurementFeatureKey`` separates subject, feature, source
qualification, and aggregate identity. ``RuntimeMeasurementDialect`` declares
how a producer encodes source names, qualifiers, aliases, and row layout. This
lets two outputs be normalised without erasing meaningful distinctions.

Row projection derives stable identities for image-, object-, and
relationship-scoped measurements. Wide and long-form tables project into the
same semantic fact model when the dialect explicitly supports that mapping.

Feature semantics
-----------------

``RuntimeMeasurementFeatureSemanticProfile`` is a most-derived context strategy
family. Feature markers and declarations select behaviour for counts,
identifiers, locations, calculated values, shapes, intensity, and other roles.
The profile owns value comparison, row-identity stability, and special
derivations for that feature family.

Numeric policy
--------------

``RuntimeEquivalencePolicy`` owns non-negative tolerances, measurement dialect,
name normalisation, missing-value behaviour, and stability rules. Feature- and
relationship-specific tolerances extend the nominal policy surface rather than
being collected in an external feature-name table.

Object and relationship alignment
---------------------------------

Object-label comparison accounts for plane/object domains and derives required
object measurements from the label values. Relationship comparison preserves
parent and child identities and applies registered alignment strategies when
object instance keys are projected across slices.

Output
------

``RuntimeEquivalenceReport`` contains typed difference records for artifact
counts, measurement features/content, tables, and images. An empty difference
tuple means the compared outputs are semantically equivalent.

Official30 evidence boundary
----------------------------

The portable acceptance definition is
``benchmark/manifests/official30_portable_axis1.json`` plus the two integration
tests in ``tests/integration/test_cellprofiler_official30_zmq.py``. The headless
test loads exactly 30 cases, requires native references, runs every case with
``continue_on_error=True``, and requires every native/OpenHCS execution to
succeed and every observation to be equivalent. The Napari test exercises the
same cases one at a time with non-persistent viewer lifecycle and functional
viewer-state checks.

On Linux, run the headless acceptance boundary under the repository-wide
runtime lock. The cache-relative path avoids coupling the command to one
developer account:

.. code-block:: bash

   mkdir -p "${XDG_CACHE_HOME:-$HOME/.cache}/openhcs"
   flock "${XDG_CACHE_HOME:-$HOME/.cache}/openhcs/official30-runtime.lock" \
     env OPENHCS_CPU_ONLY=true QT_QPA_PLATFORM=offscreen MPLBACKEND=Agg \
     OPENHCS_CP_NATIVE_REFERENCE_ROOT=<durable-native-reference-root> \
     pytest -q \
     tests/integration/test_cellprofiler_official30_zmq.py::test_official30_compile_execute_and_match_native_references_over_zmq

Use the sibling
``test_official30_nonpersistent_napari_isolated_per_case`` target for the Napari
route. Different ZMQ/viewer ports avoid endpoint conflict, but overlapping runs
remain diagnostic only and must not be reported as canonical acceptance timing.

Compared modalities and policy
------------------------------

Measurement of an OpenHCS run is separate from CellProfiler comparison. The
benchmark wrapper accepts the ordinary ``OpenHCSExecutionSubmission`` and uses
the normal compile-then-execute path. It requests either full runtime values or
outcome-only evidence through the ordinary auxiliary execution declaration,
validates the selected export and any declared axis count, and records phase
timing and provenance. Outcome-only evidence proves per-axis completion but
cannot support value-equivalence claims.
Current exports also retain the compiler's exact axis membership: a missing
compiled axis or an outcome for an uncompiled axis invalidates the run even if
every retained outcome reports success. The measured-run finaliser refuses an
empty execution. Archived outcome-only exports that predate this membership
field remain readable, but their observed axes alone cannot prove complete
compiled coverage.
Repeated measurements can share one connected ordinary execution server while
each run compiles its own artifact and retains a distinct observation and
receipt. The benchmark does not create a second execution path to keep that
server warm.

Full-value observation expectations retain the compiled axis that owns each
artifact kind. A plate-scoped export is checked on its one owning axis rather
than required independently on every image axis. Archived observation exports
keep their earlier all-axis expectation when read.

A typed completed-run receipt derives execution identity, source/configuration
digests, and output references from those same authorities;
it does not become a second job-status store. The ordinary server's runtime
observation supplies its Python and installed-distribution snapshot to the
receipt; that is server provenance, not proof of a remote worker environment.
The CellProfiler adapter prepares one such submission and then applies its
optional native-reference equivalence policy. It does not own a second execution
engine.
An agent can finalise the same receipt after a normal headless job completes:
the execution service supplies the exact submission, endpoint handshake and
server completion record, while the benchmark extension validates and retains
the observation. Both ordinary export scopes carry the producing server
execution ID. The shared finaliser rejects an export from a different job
before writing a success receipt; the runtime export writer also refuses to
replace an existing file. The benchmark finaliser publishes each evidence file
completely and exclusively, so competing finalisers cannot replace one
another's retained evidence. This protects individual files, not the entire
group of files as one transaction. It records the server's start/end time as
``SERVER_PIPELINE_JOB`` and retains the submitted compile-artifact identity,
because an ordinary execution request without one may include inline
compilation. The synchronous wrapper may additionally record client submit/wait
phases and an execution-specific interval from progress events. The completed
server job, not progress events, supplies the execution-only duration. A missing
progress event leaves that diagnostic interval absent; client wait time is not
used to guess it. Server, progress, and client wait intervals overlap, so
additive phase totals count the client submit/wait phases but not their nested
server or progress observations.

If finalisation stops between evidence files, inspection derives the
``unreceipted_artifacts`` list from the measured-artifact declarations. Their
presence is reported separately from a valid success receipt; no partial
directory is promoted to a completed measurement. Retrying finalisation for
the same completed job can reuse only byte-identical pre-receipt files. The
finaliser writes missing files, rechecks the declared set, and then publishes
the receipt. Conflicting files or an existing receipt fail closed.

For ordinary reference runs, the OpenHCS benchmark adapter builds typed
runtime/output snapshots and compares:

- images and materialised label images when image comparison is enabled
- CSV/table outputs, including measurement and relationship facts
- CPA SQLite table projections
- CellProfiler Analyst ``.properties`` values

The strict CellProfiler policy sets numeric and image absolute/relative
tolerances to ``1e-6``, permits zero differing image fraction, disables the
broad feature-specific relaxations used by less strict compatibility modes, and
applies the same policy to database export comparison. A successful observation
therefore means semantic equivalence under that declared policy, not universal
byte identity.

Pipelines that originally save no comparable values can use a benchmark-only
reference-export plan. Its inventory is derived from the importer's terminal
artifact contracts, and its digest-bound sidecar must match the exact generated
``.cppipe`` before comparison. The adapter then requires exactly one declared
file on each side for every selected artifact. Numeric image pixels use
``atol=1e-6``, ``rtol=1e-6``, and zero out-of-tolerance pixels; categorical
object labels require exact integer equality. Only the explicit native 2-D
label versus OpenHCS one-plane ``(1, Y, X)`` representation is projected before
categorical comparison; arbitrary singleton axes and true shape differences
remain failures. This sidecar records benchmark derivation and comparison
semantics; it is not an importer or runtime pipeline model.

Minimum durable receipt
-----------------------

The runner emits ``observations.jsonl``, ``observations.csv``,
``phase_timing.csv``, ``summary.csv``, and ``suite_metadata.json``. Those files
record case/suite identity, success, equivalence, difference count, numeric
tolerances, output paths, timing, platform, and native-reference root. They do
not currently record every source identity required for a durable publication
claim. A comparison run requires a new or empty destination and exclusively
claims its first typed receipt rather than replacing another run's evidence.

Retain the generated files together with a receipt containing at least:

- OpenHCS Git commit and whether the worktree was dirty
- SHA-256 of the exact Official30 manifest
- native-reference root identity plus an inventory or digest
- native CellProfiler executable/version identity
- exact command, environment flags, test target, and ZMQ/viewer ports
- suite id, start/end timestamps, host isolation/lock state, and exit status
- compared modalities and the complete equivalence-policy values
- per-case success, ``equivalent``, and ``difference_count`` fields
- for Napari, the uninterrupted-run case set and any separately targeted reruns

``summary.csv`` alone, a transient ``/tmp`` path, a test definition without a
recorded invocation, or a compatibility-matrix report is not a durable parity
receipt. If Napari cases are closed by targeted reruns, report that topology
explicitly rather than describing it as one uninterrupted all-case run.
The separate single-pipeline measured-run receipt retains the submitted pipeline
and global-configuration source documents alongside their digests. It is still
not a native-reference comparison or a suite-level publication receipt by itself.

Extension rule
--------------

New semantics belong on the authoritative measurement feature, artifact type,
dialect, relationship declaration, or registered strategy. Generic comparison
code must not hardcode concrete CellProfiler feature names or copy tolerances
into a second registry.
