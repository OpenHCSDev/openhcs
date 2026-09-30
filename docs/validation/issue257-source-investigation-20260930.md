# Issue257: produced filename and metadata address ownership

Status: source investigation and runnable failure reproducer; **not a product
fix or native acceptance**. Integration/implementation owner remains the
OpenHCS coordinator, as recorded in
`/home/ts/wt/openhcs-issue-batch-20260929/PRODUCED-FILENAME-ISSUE-20260930.md`.

Worktree: `/home/ts/wt/openhcs-produced-output-address-20260930`.
Branch: `fix/produced-output-address-257-20260930`.
Source base: `32d070c261d9bcfeb2354b70203f79a71d15ce40` (remote main including
merged255). No edits in the coordinator's255 tree, installed source, or frozen
H002B author output. No runtime/JVM/MCP/GUI, input pixels, held-out data,
downloads, installation changes, or heavy tests used for this investigation.

## Concrete cause

Two independent defects in `function_output_identity.py` reproduce the logged
destination. This is not a BioFormats reader failure: its filename parser
inherits the canonical source-schema parser.

1. `FunctionOutputExtensionAuthority.from_path` (line358) joins **all**
   `Path.suffixes`. For the valid virtual plane filename
   `image.ome.tif_s001_w1_z001_t001.tif`, that yields
   `.ome.tif_s001_w1_z001_t001.tif`, not the parser-declared `.tif`.
   `_identity_from_metadata_uncached` (line555),
   `filename_identity_from_metadata` (line673), and
   `_source_stack_source_identity` (line869) seed identities from this result.
   `_complete_identity_from_paths` (line735) later obtains the correctly parsed
   extension but prefers the already populated extension (lines757–759).
   `_source_stack_extension` (line962) similarly prefers the raw suffix-chain
   inference from the fallback path. Thus merely changing the completion
   method leaves the stacked path defective.
2. `FunctionOutputPathAuthority._qualified_filename` (line311) again joins all
   suffixes. It puts the output qualifier after `image`, rather than after
   `_t001`. Even with the correct `.tif` extension this changes the well token
   to an underscore-containing string the canonical grammar cannot parse.
   With both defects, the exact result is:

   ```text
   image_centre_dots.ome.tif_s001_w1_z001_t001.ome.tif_s001_w1_z001_t001.tif
   ```

3. `OpenHCSMetadataWriter.OutputTarget.produced_projection_metadata`
   (`function_outputs.py` lines815–834) discards the available typed producer
   address and reconstructs it by parsing this destination. It fails after
   output persistence. The strict rejection is useful evidence, not a guard
   to delete.

The explicit original failed-log access confirms execution
`648ac81c-0767-4315-909c-7cf1a8e66621` failed through
`finalize_function_step_outputs -> write_primary_metadata -> OutputTarget.write
-> produced_projection_metadata`. Evidence is lines609–628 and651 of
`/home/ts/wt/openhcs-h002-uncoached-20260929b/output/data/openhcs/logs/openhcs_zmq_server_port_5993_1790731599284689.log`.
No replay or scientific re-evaluation was performed.

`git diff --name-only 86a99f33c HEAD --` returned no changes for the identity,
manifest, outputs, source_projection, source_schema, and BioFormats files
traced here. The implicated code survives on this current source base.

## Existing owners and proposed coherent fix

The producer already owns the needed facts. `_save_outputs`
(`function_runtime.py` lines3267–3306) resolves `FunctionOutputIdentity`, applies
the named-output qualifier, constructs the path, and builds
`ProducedOutputSemantics.from_output`. That record inherits semantic
`component_values` **and separate** `filename_component_values`, extension,
qualifier, plus producer identity, relative path and payload metadata
(`function_output_manifest.py` lines128–217).

Keep these authorities; do not add another filename/address registry.

- Resolve extensions at the existing identity boundary using
  `_parsed_path_identity_with_cache` / `FilenameParseResult.extension` for
  canonical plane paths. Do not seed a suffix-chain guess before a successful
  parser result, or allow the stacked fallback path to override it. Keep
  explicitly declared extensions under their owner. For a genuine physical
  source path that is not a canonical plane name, use existing declared image
  format/source metadata authority; do not confuse its basename with virtual
  plane coordinates. Check all five `from_path` call sites and
  `_source_stack_extension`, rather than repairing only the observed caller.
- Have `filename_for_identity` retain the bound `FilenameParseResult`; give
  `_qualified_filename` that declared, normalized extension. Insert the
  qualifier immediately before **that extension**, not before every dot in
  the basename. Preserve dotted well identity and supported compound
  extensions. Do not replace this with a new regex or rename source wells.
- Derive the saved filename address on the existing `FunctionOutputIdentity`
  / `ProducedOutputSemantics` owner from `filename_component_values` when
  present, otherwise `component_values`, through the existing canonical
  component binding and `OpenHCSPlaneAddress` constructors. Missing coordinates
  must remain errors; do not infer axis values. Metadata publication consumes
  this typed address. Semantic `component_values` still feed source metadata;
  do not restore collapsed dimensions from filename coordinates.
- Validate rendered filename/address agreement once at the producing path
  boundary, before saving. The existing
  `SourceProjectionMetadataSerializer.virtual_path` (source_projection.py
  line1130) already demonstrates parser round-trip validation against the
  original typed address. Validation checks the record; it must not become the
  authority from which publication reconstructs the record.
- Preserve actual persisted header/dtype/calibration reads in
  `OutputTarget.persisted_image_metadata`, source lineage, uniqueness checks,
  and same-address named-output `SourceArtifactProjection` aliases.

There is a second publication consumer to cover in the same fix:
`OutputTarget.write` invokes `OpenHCSMetadataGenerator.create_metadata` before
merging the typed projections. That generator inventories saved files but
reparses them for component keys (`openhcs.py` lines1114–1232); unmatched names
are silently skipped (line1209). Route produced-file component inventories
through the retained typed records / durable typed projections, filtered to
actual saved paths. External disk discovery remains a legitimate parsing
boundary, not a legacy adapter for malformed generated names. Preserve
`finalize_completed_plate` reconciliation when the live manifest is no longer
available: it must retain the existing durable source projections, not rebuild
coverage from input-cache keys or add a second store. Trusting the record
alone without correcting filenames would leave saved readback broken.

## Runnable source-light reproducer and limits

```sh
cd /home/ts/wt/openhcs-produced-output-address-20260930
/home/ts/code/projects/openhcs/.venv/bin/python -B tools/reproduce_issue257_filename_identity.py
```

Executed successfully, exit0. The probe executes the **actual AST-selected
helper declarations** for extension inference and qualification; it reads the
actual canonical address-owner regex. Supplying the inferred extension to
filename construction is explicitly modeled from a canonical fixture. It does
not import OpenHCS, run the actual parser module, compile a pipeline, inspect
arrays, invoke pytest's runtime-cleanup fixtures, or prove native acceptance.

Five fixtures: plain and plain compound-extension controls both pass; dotted
well, OME-named well, and dotted-well compound-extension cases each reproduce
both extension disagreement and qualification-only parse rejection. The
OME-named fixture matches the original failed basename exactly. This is a
failure-reproducer success, **not a fixed-product test pass**. Machine-readable
summary and source hashes are in `issue257-source-receipt.json` beside this file.

Coordinator acceptance after the currently owned live slot is available:
tiny synthetic OME-TIFF, ordinary typed identity image plus artifacts, image
publication enabled, plain/dotted names and first/chained source lineage;
complete/reordered/reduced Z coverage; ordinary current compile -> execute ->
saved inventory/readback. Require generated filenames to round-trip to retained
addresses, correct alias projections, saved calibration/dtype/source lineage,
and metadata coverage of only persisted outputs. No original failed-job replay,
assay data, expected counts, or biological hints are needed. A filtered-out
image run is not acceptance.

## Instruction receipt / architecture coverage

Read completely: managed `nra-refactoring/SKILL.md` and
`refactor-audit/SKILL.md`, plus authoritative archive members
`refactor-audit/SKILL.md`, `references/patterns/README.md`, all six catalogs
(`implementation.md`, `membership.md`, `boundaries.md`, `identity.md`,
`over-time.md`, `agent-defaults.md`), and `references/surface-receipt.md`.

- `/home/ts/.codex/skills/nra-refactoring/SKILL.md` SHA256
  `9f2f8b28bc82256eefa3e9d63248c50722dc3ffe7d77adba5793296df196b47e`.
- `/home/ts/.codex/skills/refactor-audit/SKILL.md` SHA256
  `5da7af7f7bfff29a15a248c70a0759b4be1d76039ade9d22232b791ea1cba8d4`.
- `/home/ts/code/projects/nominal-refactor-advisor/skills/refactor-audit.skill`
  SHA256 `100fbe8ef89664b866777e87b2c8640a3432e8a10e9188dff81c97942d551bf6`.

The proposal applies BOUND-4/BOUND-2 (flattening and bypassing typed owners),
IDEN-1 (semantic identity versus storage address), IDEN-5 (no duplicate
authority), and TIME-9 (no permanent fallback adapter). Scope is this traced
publication surface, not a repository-wide NRA scan, audit certificate, or
architectural correctness claim. No production patch or competing draft PR
was opened; the coordinator retains the coherent fix and native acceptance.
