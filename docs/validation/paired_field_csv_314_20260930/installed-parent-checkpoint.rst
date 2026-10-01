Installed paired-field export acceptance
=======================================

Parent integration owner. Production candidate d8fa0d5afd690cb1d37b7dd49012d1e0e8035716
normally integrates main8e478cb21f89fe74c3d6ead0cb54c67a5e1047dc with PR317.
This checkpoint supersedes source-only limits without erasing their original
failures or claiming biological acceptance or full ZIP-refactor completion.

Issue322 reproduces on both metadata-bearing connected-component and preserved
label inputs: two rich-image cases fail at ``image.copy()``, while both plain
array controls pass. The existing runtime payload already owns NumPy conversion.
Replace that consumer-only array-method assumption with ``np.asarray(image).copy()``.
Keep the original image in main flow and SourceImageObjectLabelBuildRequest,
preserving pixels, source identity, domain and declared spacing. No carrier
forwarding method, type/name switch, metadata mirror or fallback is added.
BOUND-2/BOUND-7 prevention uses the declared conversion owner instead of bypassing
the carrier or probing/adding private array attributes. This is an authored
boundary repair, not an NRA-produced equivalence proof.

Current source checks: 51 tests pass across object-output contracts, source-image
identity policy and the real spreadsheet exporter. Four additional rendering
regression controls pass. The new rich/plain cases retain exact labels, object
counts, areas, untouched input pixels, original main-flow identity, provenance,
spatial domain and configured 0.65 XY spacing. The unchanged packaged structural
ratchet compares 5,133 metrics against current main with zero positive deltas.
Earlier full-context NRA/R1 deadline failures remain incomplete, not passes;
the owner explicitly directed that these not block verified useful checkpoints.
An initial source invocation used a nonexistent test filename and ran no tests;
its exit4/XML are retained and excluded from the 55-pass count.

Persistent evidence::

    /home/ts/wt/openhcs-issue-batch-20260929/paired-field-parent-20260930

Build/install uses the actual OpenHCS wheel and its recorded ArrayBridge409b1e0
companion wheel in the isolated candidate environment. Heavy third-party packages
and Fiji are reused; download is disabled and shared main/installations unchanged.
Fresh MCP health reports site-packages, all 56 packaged resources and no stale
source. The original failed installed run029ec591 remains retained independently.

The first receipt helper exits at its PTY's 4,096-byte canonical input limit
before parsing or dispatching the artifact-plan request. Its native startup
handle149206/create1790814373.81 remains live. A new MCP client150535 reconnects
with noncanonical, echo-disabled terminal input and observes that same child
through readiness. Startup, preparation and execution are not replayed. Ordinary
10-second observation deadlines are unchanged. Native cold preparation takes
about119 seconds; this is explicit preparation, not a raised per-command timeout.

After the copy repair, executionfa80b527-a1c4-4f00-846c-28164f7a1b27 passes
KnownNuclei and fails at the next step: the parent's synthetic control left
KnownCells on PREVIOUS_STEP although it requires original Actin-channel main
flow, absent from the DNA-only predecessor. The reflected processing-config
schema and existing CellProfiler importer confirm that named artifact binding
does not select main-flow input. Correct only the fixture's existing lazy
``processing_config.input_source`` to PIPELINE_START. Preserve this failed
run and use ``outputs-input-source-fixed`` rather than overwriting its files.
No scientific parameters, algorithm or production source-selection guard change.

The fresh complete PipelineDocument retains all source aliases/coordinate rules,
two wells, one worker and all four analysis/export steps. Artifact inspection
finds four source files, two axes and eight per-axis step plans without errors.
Compile14d9ac41-4b55-4c88-93a4-02ae04de50e9 completes in0.79 seconds.
Executionbb932c48-de7a-4867-bbb2-5a090a5aa928 completes in1.11 seconds, including
strict final metadata reconciliation. Reconnected receipt017 is terminal success.

Read-only installed ``check-installed-parent.py RECEIPT_ROOT`` verifies:

* MCP's explicit result-directory route returns all16 persisted result files
  without truncation, including four complete Cells.csv rows rather than eight
  split partial rows. Native bounded CSV previews agree exactly with disk.
* Image numbers1/2 each contain objects1/2. Parent_Nuclei, location and shape
  coexist in every cell row; all fields are populated. Areas are52 pixels each;
  location and shape centres agree at6.5/23.5 pixels. Fields are not collapsed.
* Four physical label references reopen through the existing workspace projection
  with disk addresses and32x32 spatial domains. Nuclei labels match the known
  masks exactly; both cell IDs contain52 pixels each. All four synthetic raw
  images retain their fixture pixels unchanged.
* The existing ZMQRuntimeExecutionObservationExport reader reopens the actual
  gzip-pickle observation (the extension is not its format authority) and
  verifies both wells succeeded and the exact execution ID. No new reader.

The checker initially counted aliased lookup keys as physical files; the native
projection intentionally admits relative/full aliases. The corrected assertion
counts distinct backend addresses and requires each declared source projection.
No CSV, label, source-pixel or completion assertion was removed.

This manually declared generic source-binding fixture omits source_voxel_spacing;
its HTD text alone does not calibrate the generic declaration route. Do not
claim installed physical-unit acceptance from it. The rich-input unit control
proves declared spacing is preserved; this installed control proves field/row
identity and original pixel-coordinate semantics only. Biological raw/result/
combined QA, calibration of future trials and fresh blind analysis remain separate.

Owned runtime close in receipt021 reports request_attempted, acknowledged and
process_exited true for149206/create1790814373.81. MCP150535 exits normally;
independent process/socket checks confirm both gone and ports5997/6997 free.
No viewer was launched, desktop:0 and H002 untouched. Runtime logs/settings are
archived in ``runtime-image-copy-fixed-logs.tgz`` before removing only owned
18MiB scratch and20MiB generated build output. All scientific output, failed
attempts, requests, receipts, wheel candidates and persistent source are retained.
H003e remains immutable REJECT with no data access, rerun, tuning or answers read.
