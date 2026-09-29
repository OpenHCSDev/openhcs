# Explicit materialized result review

Base:OpenHCSDev/openhcs main0c7b898f852a8bedc0e1bc38b93f36088d301808.
Tracking issue:#134. This is an implementation workstream, not a completed fix.

Observed: actual typed measurement outputs carry disk locations outside the
default result directory. Public inventory/existing-file stream does not
resolve that declared directory and fails handler detection or file lookup.

Complete the existing ownership route from materialization identity/location
through authorized bounded CSV/ROI inspection and managed-viewer reopening.
Preserve source/axis/object/provenance and path policy; do not mirror an
artifact registry, relocate files, or rerun scientific analysis. Trace existing
declarations/implementations/consumers before deciding whether to extend the
current request boundary. One shared mechanism, no per-extension dispatcher.

Remaining: complete NRA dependency/raw-record coverage and declaration-owner
receipt; implementation; family-level bounded/path/provenance regressions;
fresh-process synthetic MCP/viewer proof; review and remote publication.
Source/native proof and live biological evidence are distinct.

Write scope: plate/result inventory and inspection service/DTO/tests. Viewer
orientation is a separate workstream. Capability declarations are a potential
crossing: coordinate before altering shared classes or import regions.
The dirty shared checkout, frozen analysis, live UI and viewer remain untouched.

## Implementation-worker checkpoint

Head audited: `83ebf67195e9bfe8fa1e30770d7db68bf4a080a5`, draft PR #153,
branch `fix/mcp-materialized-result-route-20260929`. This checkpoint is reference
evidence and an explanation of the remaining boundary, not a completed audit or
implementation. No Python source has been edited and no test, image load,
scientific execution, GUI operation or MCP connection has been performed.

### Source and dependency context

The assigned worktree was clean. The eight recorded dependencies initially had
empty worktree directories. Independent clones were checked out inside this
worktree at its recorded gitlink revisions, without registering submodules in
the shared repository configuration or changing gitlinks:

| Dependency | Revision |
| --- | --- |
| ObjectState | b0004daf3223326ac78689ba7b2e68abc18ae298 |
| PolyStore | 0efe67fdd14985bf90cee6e0f0c4735d41d265d1 |
| arraybridge | fddd9857bcd21468d20bc8547a769e0c6c9f1906 |
| metaclass-registry | ca0a87e873f929b311a87a4d60cd3bfba315dbcf |
| pycodify | 792b03413331fdf107e369c924c257a2f0b16126 |
| pyqt-reactive | a51c3d965f8ffdefe95a2b4b37347a85341d483a |
| python-introspect | 5bb79d5edb7250083a09ab77b2d9177e3ba202ab |
| zmqruntime | 1d3b32f4fcead23d5d2079c975eb2ae7646a1478 |

NRA source: `/home/ts/code/projects/nominal-refactor-advisor` at
`52fe8b4666a20583f0ddf8ed3b7a9e89857e4809`; its existing unrelated dirty files
were untouched. Scanner interpreter: that checkout's `.venv/bin/python`,
CPython 3.11.11. OpenHCS permits Python >=3.11,<3.15. Census/overlay interpreter:
`/usr/bin/python`, CPython 3.14.6. No OpenHCS runtime import environment has yet
been validated. Future tests must put this worktree and its own dependency
`src` directories on `PYTHONPATH`, never a shared-checkout editable install.

### Scan coverage and resource stop

Receipts and task cache root: `/tmp/openhcs-pr153.LeLQct`. The inspected actual
CLI accepts `--json --raw-findings --json-payload full`, repeated
`--context-root`, `--parse-workers 1`, `--analysis-workers 1` and
`--scan-budget-seconds`. Positional scope was all `openhcs`; explicit context
was all `openhcs` plus all eight dependency `src` roots above. Tests were
excluded by the CLI default. This is the requested scan scope, not evidence
that the scan completed or that every third-party import was resolved.

- `scan-before.json` reports `deadline_incomplete`, `complete: false`,
  `deadline_exceeded: true`, stage `parse_python_module`, budget 20 seconds.
  Exit 124, elapsed 21.11 seconds, peak RSS 629624 KiB. The CLI help described
  the budget flag as economics-only, but current CLI execution also applies
  its default deadline to ordinary scans.
- The explicit 900-second retry was stopped by the worker with SIGTERM after
  RSS exceeded the 768 MiB resource envelope. It produced no JSON findings.
  Shell exit 143, elapsed 68.62 seconds, peak RSS 1604952 KiB. Preserve
  `scan-before-900.stderr`; the timing wrapper's final exit-status field is
  not a completed scan receipt.
- Detector coverage, omitted-detector counts, R1 `mapping_read` and
  `unmodeled_record_shape` evidence, and source/declaration pairs for
  `redundant_type_check` remain unavailable. Empty or absent findings are not
  a clean architecture verdict. No Python edits may start on these receipts.
- Request a resource-approved complete scan before implementation. Do not
  substitute `focused_local_partial`, exclude production owners, suppress a
  failure, or claim global proof from the census/overlay.

The full-package census completed with no unparsed files: 6.98 seconds,
47224 KiB peak RSS. Relevant starting measurements follow; these are structural
leads, not domain findings or permission for unrelated refactoring.

| Surface | Code lines | String-key subscripts | Long chains | Chain terms |
| --- | ---: | ---: | ---: | ---: |
| core/plate_image_inventory.py | 1277 | 3 | 0 | 0 |
| agent/services/plate_inspection_service.py | 2059 | 2 | 3 | 13 |
| agent/dto/plate.py | 1067 | 0 | 0 | 0 |

The full-package overlay completed in 56.39 seconds, peak RSS 598356 KiB,
exit 0, without parse warnings. Its relevant source-checked leads include
the 114-line `_query_files` handler-first procedure and the CSV reader's
`fallback_columns` header heuristic. Neither is R1 raw-record evidence. Raw
renderer shapes elsewhere in its report are outside this assignment.
At the final resource check available RAM was 9997 MiB, but memory PSI full
was 2.82% (10-second average) and 1.14% (60-second average). Stop new heavy
loads until main approves the workflow and the pressure condition clears.

### Owner trace and proposed migration closure

The observed failure is a location/identity boundary, not absent scientific
output. Pattern leads: IDEN-5/IDEN-6 (materialized identity versus rebuilt
layout) and BOUND-2 (consumers bypass a richer typed runtime owner). There is
no claim that NRA has proved these leads.

- `PathPlanner._cached_results_path` in `core/pipeline/path_planner.py:2891`
  preserves absolute `materialization_results_path` and resolves relative
  paths under the planned output plate root.
- `PlateResultFileInventory.configured_output_result_directories` in
  `core/plate_image_inventory.py:745` derives directories instead from
  `path_config.sub_dir` and `analysis_results_dir_for`. Its result records
  carry paths and filename-derived metadata, not `RuntimeArtifactAddress`.
- `RuntimeValueStore`, `StoredRuntimeValue`, `RuntimeArtifactAddress` and
  `RuntimeArtifactLocation` in `core/runtime_stores.py` own semantic artifact
  keys, axis scope and storage addresses. `address_matches_plan:817` checks
  name/type, axis, group and planned location; path readability alone does not.
- `RuntimeArtifactMaterialization.from_record:1078` and
  `outputs:1154` in `core/steps/function_artifact_materialization.py` derive
  exact writer outputs from the compiled output plan and runtime record.
  `observed_materialized_artifact_locations_by_address:1325` projects this
  authority into address/location pairs. A planned candidate path is not a
  confirmed writer-success receipt; establish that distinction before using it.
- `LiveMeasurementTablePreview` in `core/progress/live_measurements.py:53`
  retains the artifact address, materialized locations, schema, object and
  source names. The generic `RuntimeArtifactProgressPayload` in
  `core/progress/runtime_artifacts.py:23` currently carries addresses only.
  Determine the authoritative available execution observation route before
  extending it. Do not introduce a sidecar, duplicate registry or manifest.
- `PlateInspectionService._query_files:1114` still reaches handler detection
  when the reconstructed result-only inventory is absent.
- `PlateStreamingService.stream_files:83` resolves `open_context` before saved
  file identity and then relies on `context.handler` for the primary backend.
  First-class result-only reopening needs a coherent change here, not a fake
  microscope handler, basename matching or a compatibility fallback.
- `QueryPlateFilesCapability` and `StreamPlateFilesToViewerCapability` in
  `agent/capabilities.py:2067` and `:2123` derive their public contracts from
  existing request declarations. Verify installed/current MCP projection
  after coherently updating those declarations.

Proposed destination: extend the genuine runtime materialization authority and
derive the public result inventory from it. Preserve the exact key, source,
axis/object provenance and output identity through query and stream consumers.
External CSV and ImageJ ROI archive formats remain unchanged. Attach bounds
and AgentPathPolicy checks at the inspection/reopening boundary. No nominal
carrier alone resolves the competing location authorities.

The existing CSV preview reader materialises the bounded-byte file's complete
row sequence and heuristically searches for a header (`:602`, `:622`). Replace
that heuristic for admitted typed measurement outputs with a schema-bearing,
bounded native read; do not silently accept a foreign header or identity.
ROI preview currently uses the native PolyStore archive reader (`:495`), which
should remain the external-format owner.

### Crossing requiring main's direction

The listed write set excludes `agent/services/plate_streaming_service.py`, but
its pre-resolution handler dependency is directly on the reopening path.
Request this one-file scope extension before editing it. It is not Jason's
viewer-orientation surface. No changes to `capabilities.py` have been made.
Jason's supplied session ID was not registered on the available agent-comms
bus, and this worker has no direct session-message tool. Main must provide a
direct route or relay the proposed plate-capability import/declaration crossing
before overlapping edits. Do not manufacture a second messaging/runtime path.

### New-case experiments, guards and completion gates

Before: changing a materialization root changes the actual writer path but not
the inspection directory reconstructed from path planning. After: changing the
existing materialization declaration must suffice; inspection and reopening
derive locations from the same authoritative observation without another
consumer-side root declaration. This experiment is proposed, not executed.

Required synthetic family tests cover default/relative/absolute roots; exact
typed identity and foreign identity/path rejection; denied/symlinked paths;
bounded CSV schema and rows; label and point ROI object identity and exact point
position; no microscope discovery, BioFormats startup, image reload or science
execution on the result-only route. Check malformed schema, truncated previews,
multiple output planes and aggregate axis/object provenance.

Guards: no new independently maintained artifact directory/identity registry;
no basename admission for typed results; no raw-string extension ladder,
`getattr` defaults, Protocol replacement or silent fallback; retain existing
path policy and strict boundary validation. Review the full migration closure,
then apply declaration-targeted transformations through a revision-checked NRA
transaction. Behavioural additions and unsupported native proof obligations
must be labelled explicitly, not described as equivalent-body proofs.

Done only when complete pre/post dependency scans and R1 receipts are available,
native bounded regressions pass, the installed/current public MCP contract is
verified, and an isolated tiny fresh-process synthetic reopening succeeds.
None of those implementation/test gates is complete at this checkpoint. Live
analysis integration and biological QA remain main's independent frozen route.
