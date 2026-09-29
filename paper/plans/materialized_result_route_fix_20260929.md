# Explicit materialized result review

Base:OpenHCSDev/openhcs main0c7b898f852a8bedc0e1bc38b93f36088d301808.
Tracking issue:#134. This is an implementation workstream, not a completed fix.

## Current owner checkpoint: native codec delivered

This section supersedes the historical FULL-audit implementation hold below.
The user explicitly authorized bounded NRA queries plus refactor-audit census
and overlay, keeping global FULL/R1 coverage and native proof gaps distinct.
Integration owner: main OpenHCS blind-analysis coordinator. Persistent worktree:
`/home/ts/wt/openhcs-materialized-result-route-20260929`.

OpenHCSDev/PolyStore#13 is merged. Recorded dependency main:
`e430c331ad931edc92dfe9d4fcd0d837a3cfeea8`. The parent gitlink is being advanced
to that reviewed merge. The existing codec declarations now own native ImageJ
POINT/polygon/polyline/oval encode/decode; the ZIP reader no longer substitutes
PolygonShape for unrelated geometry. Exact subpixel points and all points in
a native member survive. Malformed one-point FREEHAND archives stay invalid;
no legacy reader, axis guess, or frozen-data rewrite is added.

All 114 ROI/disk/streaming metadata and identity tests passed on source overrides,
then again against installed wheels outside source roots: installed test run
0.81 seconds, wall 1.33 seconds, peak RSS 104,272 KiB. Fifteen existing parent
streaming/materialization tests also passed in 5.26 seconds, with two expected
pytest configuration warnings because plugin autoload was disabled. These are
sanity checks, not live viewer or scientific acceptance.

Isolated installed environment and disposable cache:
`/home/ts/.cache/agent-scratch/openhcs-point-codec-20260929`. Its small live venv
installs this parent and its eight pinned dependency wheels while borrowing
unchanged scientific libraries from the existing OpenHCS environment. Actual
OpenHCS, PolyStore, arraybridge and ZMQRuntime imports resolve inside that venv,
not source overrides. Shared packages and the dirty main checkout are unchanged.
An initial no-build-isolation install failed on absent hatchling; the ordinary
declared isolated builds completed. Fresh installed MCP health is OK, with
56 packaged resources present and no stale source or missing resource warnings.

Installed MCP to the existing viewer on TCP 5690 is NOT validated: native pickle
decoding fails on ViewerWindowGeometry, a type in the dirty shared viewer source
but absent from recorded main. The old viewer and its visible evidence are
preserved; do not add a compatibility alias. A matched-version, tiny synthetic
managed viewer is the next live check. Original H002 scientific results remain
frozen and biologically ambiguous.

Before extending materialization writer/worker observations, coordinate with
the active OpenHCSDev/openhcs#157 owner: that PR changes worker_execution,
runtime_exports and function_artifact_materialization to retain outcome export
paths after cleanup. Its string path outcome is useful integration context but
not yet proof of a provenance-bearing writer-success receipt for #134.
The explicit result-directory inventory/reopening fix and orthogonal viewer
control remain unfinished; this checkpoint does not close #134 or PR #153.

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

- `_cached_results_path` in `core/pipeline/path_planner.py:2891`
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

### Approved crossing and remaining coordination

Main approved `agent/services/plate_streaming_service.py` as an extension to
this write set because its pre-resolution handler dependency is directly on
the reopening path. This is not Jason's viewer-orientation surface. No changes
to that service or `capabilities.py` have been made.
Jason's supplied session ID was not registered on the available agent-comms
bus, and this worker has no direct session-message tool. Main must provide a
direct route or relay the proposed plate-capability import/declaration crossing
before overlapping edits. Do not manufacture a second messaging/runtime path.

Proposed capability crossing sent to main: plate declarations
`QueryPlateFilesCapability:2067` and `StreamPlateFilesToViewerCapability:2123`,
including their descriptions/data-exposure metadata if the request changes.
The existing plate DTO import block at line 95 already imports both request
types; no additional import or viewer declaration change is proposed. Main
subsequently reported Jason terminal, with no competing scan. His native-only
diagnosis is separate evidence, not this worker's managed/plugin/MCP proof.

### Conditional scan recovery checkpoint

Audited Python remains identical to initial HEAD; current documentation-only
head is `e9c767a572b51d10faeb5bafc5840b39492cc0d7`. NRA remains at
`52fe8b4666a20583f0ddf8ed3b7a9e89857e4809`. A bounded declaration-only import
of NRA confirmed 79 registered detectors and zero AST-retaining context
detectors. CLI `JsonPayloadSections.compact_analysis_compatible` and
`analyze_compact_roots_with_cache` therefore permit a complete compact scan
for this detector roster; this eligibility check is not a completed scan.

Main authorised one global scan under a conditional 2048 MiB RSS envelope,
only after at least 11 GiB available and memory PSI full avg10 <=1% hold for
10 seconds. Stop conditions are available memory below 8 GiB, PSI above 1%
for 10 seconds, RSS above 2048 MiB, or the initial 165-second shell shard.
The ordinary 768 MiB test/Qt increment limit is unchanged.

The guarded launch attempt at 2026-09-29T03:58:54Z exited 78 before starting
NRA: 10343272 KiB available, PSI full avg10 0.00. Its exact receipt is
`/tmp/openhcs-pr153.LeLQct/scan-recovery-agent.guard`. No scan process or live
scan handle remains. The owned `guarded-scan.sh` retains the full production
context and worker counts above, with a 160-second internal budget and
165-second shell guard. The next proposed cache-populating profile is
`summary`, which omits graph/recipe presentation work but retains the complete
detector analysis and raw findings. It does not replace required
`--json --raw-findings --json-payload full` evidence. A subsequent full export
must authenticate identical source/configuration identity and disclose any
source-index/observation/raw-record omission. No partial scan permits Python
implementation or resuming Jason as though the common audit were complete.

Additional source-checked authority limits:

- `StepExecutionObservation:44` already declares materialized address/location
  receipts, but `finalize_function_step_outputs:128` returns `None` and
  `worker_execution.py:1000` discards `step.process`'s return. Progress locations
  are regenerated from plans/records, not propagated from successful writers.
  An annotation is not a genuine success receipt.
- `OpenHCSMetadataWriter.OutputTarget.runtime_artifact_projection_paths:878`
  projects only image paths through `ImageFileFormat.is_image_path`. Its
  existing source-projection metadata is not currently a CSV/ROI identity
  authority; do not present its image projection as proof for result files.
- Pinned PolyStore `roi.py:581` reconstructs every non-polyline ImageJ archive
  shape as `PolygonShape`. `PointImageJROIShapeConverter:547` writes one point
  without explicitly setting `ROI_TYPE.POINT`. The existing dependency owner
  needs native verification and a separately approved dependency change if
  exact point-kind reopening fails. No local duplicate decoder or submodule
  gitlink change has been made. This is not a rerun of Jason's diagnosis.

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

## Native diagnosis and audit recovery receipt, 2026-09-29

Source remains unchanged from the initial Python snapshot. Documentation head
before this receipt: `4d83353411f6376e9abc36a94ce99ee08e47b190`.
Main additionally approved existing writer/finalisation/worker observation
owners where necessary to propagate actual successful materialization receipts.
No production source, pinned dependency clone or gitlink has been edited.

The successful-save boundary is
`processing/materialization/core.py:BackendSaver.save_all:1666`: it filters
backend acceptance and calls `filemanager.save_batch` for supported batches.
`materialize:4111` returns only a primary-path string, not an address/location
receipt. Receipt propagation must originate from accepted batches after saves
return successfully, not recreate outputs or admit unsupported candidate paths.

### Scan attempts and profile

- The smaller-envelope compact summary passed the >=9 GiB/PSI gate but was
  terminated at sampled RSS 789612 KiB. Exit 143, 25.45 seconds, timing peak
  789320 KiB; no JSON findings. Receipt stem:
  `/tmp/openhcs-pr153.LeLQct/scan-recovery-summary-768`.
- All nine positional report roots plus the same nine explicit context roots
  normalise to `report_roots=()` and `has_report_filter=False`. NRA's loaded
  `AnalysisPathScope` confirmed this without analysis. This preserves every
  production owner and reports dependency findings too; it is not an exclusion.
  The initial argument-order error is preserved separately at
  `scan-recovery-summary-all-roots-768` (exit 2, no analysis).
- Corrected all-root argv hit NRA's 160-second deadline: JSON `complete=false`,
  reported stage `startup`, 160.89 seconds, timing peak 284280 KiB. Receipt stem:
  `/tmp/openhcs-pr153.LeLQct/scan-recovery-summary-all-roots-argv2-768`.
  Its guard's separate exit 127 resulted from editing the running Bash file;
  preserve that error, not as NRA's exit code. NRA stderr records exit 124.
  The guard now captures wait status explicitly and remains unchanged while live.
- Sibling py-spy attachment was permission-denied; no elevation or retry.
  The first child-profile guard failed on an uninitialised RSS variable before
  recording; its receipt is preserved as `scan-recovery-all-roots-profile-768`.
  Both recorded child PIDs were verified absent before correcting the guard.
- The corrected py-spy-child profile produced 199 samples and zero sample
  errors over 20 seconds, elapsed wrapper time 21.33 seconds, sampled aggregate
  scanner/profiler peak 109692 KiB. Former profiler/scanner PIDs 3573210/3573211
  were absent and `scanner_live_after_cleanup=false` is recorded. Receipt stem:
  `/tmp/openhcs-pr153.LeLQct/scan-recovery-all-roots-profile-supervised-768`.
  Its `.json` file contains profiler stdout, not an NRA JSON completion receipt.
  The profiler completed, but NRA emitted no scan result before the child ended.
- Main invoked the separately authorised FULL/2048 MiB guard at
  2026-09-29T04:27:58Z. It exited 78 before launching NRA: available memory
  11330576 KiB, PSI full avg10 0.00, below the 11534336 KiB (11 GiB) start
  threshold. Exact receipt:
  `/tmp/openhcs-pr153.LeLQct/scan-recovery-full-2048.guard`.
  No FULL scanner started and no FULL JSON/stderr was produced. This is a
  pre-launch gate attempt, not an executed 2048 MiB FULL scan. The allowance
  remains unused. The worker remains terminal while Jason's diagnostic runs;
  main owns any subsequent launch authorisation/invocation.

Observed inclusive stacks in that initial 20-second window:
`build_compact_projection_shard` (NRA `analysis.py:1101`) 159/199 samples;
`collect_family_batch` (`ast_tools.py:2268`) 95/199;
`store_items` (`ast_tools.py:2153`) 59/199;
`collected_family_items_content_signature` (`ast_tools.py:1924`) 42/199.
These overlap and are not additive. They identify collection/cache-signature
work in the sampled window, not the whole 160-second hot path or proof that
the deadline's `startup` label describes its actual computational stage.

All 79 detector declarations remain requested, but completed detector counts,
omissions, R1 raw findings and full source-export evidence remain unavailable.
No partial cache, successful profile, census or native diagnostic authorises
Python implementation or resuming Jason on a completed common audit.
In this NRA revision the ordinary FULL profile requests source-index,
observation/fibre and recipe sections, which exclude the compact-analysis
branch. Cached findings do not discharge those export obligations. No missing
sections or coverage status has been fabricated to bypass the gate.

### PolyStore prerequisite and native codec evidence

Main accepted the native defect and opened OpenHCSDev/PolyStore#12. Its separate
owned worktree is `/home/ts/code/projects/polystore-point-roi-20260929`, branch
`fix/native-imagej-point-roi-20260929`, tracking head
`05c4e7d1e01490b4f05fc68d55cf0d9451f54148`, draft PR #13. This is documentation
only. Its base and the parent scan's unchanged clone remain
`0efe67fdd14985bf90cee6e0f0c4735d41d265d1`. Dependency production repair is
approved only after the full NRA/R1 gate; parent gitlink integration requires
validated dependency merge and main's explicit recorded-SHA authorisation.

The actual native codec run has three cases: polygon control passes, production
point archive and independent standard POINT archive both fail with
`Polygon must have at least 3 vertices, got 1`. First completed diagnostic:
0.39 seconds, peak 53168 KiB; canonical JSON-metadata repeat: same outcomes,
0.28 seconds, peak 51808 KiB. The earlier missing-numcodecs import failure is
separate and not codec evidence. Source/version receipts verify own pinned
PolyStore/ArrayBridge/metaclass-registry/ZMQRuntime imports; CPython 3.14.6,
NumPy 2.5.1, PolyStore 0.2.19, roifile 2026.2.10, numcodecs 0.17.0.

Production POINT encoding is FREEHAND. Exact native XY `(3.5,1.25)` and logical
metadata label/object/source/plane index 2 survive serialisation; native Z is
unset. The independent POINT fixture preserves native one-based Z=3 and XY
through roifile before PolyStore decoding fails. Canonical expected metadata
comes from public `roi_zip_metadata_payload` plus JSON decoding. These native
codec diagnostics neither exercise artifact admission nor prove managed
streaming, MCP, viewer orientation or scientific correctness.

Exact codec receipts: `/tmp/openhcs-pr153.LeLQct/` with stems
`scan-recovery-point-native-prerequisite-768` and
`scan-recovery-point-native-canonical-768`. Only tiny synthetic archives were
written. Production files, frozen analysis and live viewer processes were not
loaded or changed.
