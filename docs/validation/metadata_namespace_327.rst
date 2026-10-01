Issue327 source-only namespace checkpoint
========================================

Parent is overall integration owner. This source implementation owns only the
metadata namespace/configuration boundary. Audited OpenHCS PR206 is
a3179b214b888308133e55682e964f77c2781879; PolyStore PR16 is
4939979978439a6f38145788df9aac3bce65bc70. Dependency draft PR20 extends PR16;
this application draft stacks on PR206 and pins the reviewed child source.
No parent/foreign worktree or installation was edited.

Diagnosis, witnesses, destination owners
---------------------------------------

Original openhcs/__init__.py:20 projected POLYSTORE_METADATA_FILENAME through
an ambient environment default. Existing OpenHCSMetadataConfig at
core/virtual_workspace_metadata.py:39-59 owned the actual application filename,
metadata path and managed lock paths. Existing PolyStore MetadataConfig at
metadata_writer.py:54 owned a separate frozen generic config. Its workspace
reader at virtual_workspace.py:242 used the earlier-decoded generic singleton,
not the application's already richer owner. The sole application constructor at
microscopes/microscope_base.py:469 did not supply that owner.

BOUND-2: bind the existing richer application's typed declaration instead of
reading an unrelated ambient dependency namespace. IMPL-13: shared metadata
path/lock implementation now lives once on MetadataConfig; the application
inherits it. TIME-7: delete bootstrap projection of another consumer's defaults.
No new namespace enum, string/type dispatch, mirrored config/store, singleton
mutation, filename copy, alternate reader, compatibility alias or test switch.

Library workspace construction, persisted reopen and native PicklableBackend
connection parameters carry the exact frozen MetadataConfig value. FileManager
retains its existing declaration-derived backend discovery and worker registry
reconstruction. Native dictionary decoding uses constructor keyword binding;
the get_connection_params declaration is the sole producer of its two fields.
Generic default and helpers share their existing immutable generic owner.
Application config declares only its filename/default factory; common keys,
timeout and path/lock behavior are inherited, not copied.

Durable metadata paths and structured SourcePixelRef JSON remain unchanged.
Runtime handoff records are produced with the current typed config. No data
conversion, namespace negotiation, environment workaround or legacy reader.

New-case test and source checks
------------------------------

A third namespace now needs one MetadataConfig declaration/value and constructor
binding, not coordination of bootstrap timing and separate consumer defaults.
The library new-case test changes filename and subdirectory-key declaration to
collections, then loads exact pixels without changing any consumer/registry.
Site guards reject a workspace global path lookup, require the retained owner
and native keyword binding, prove inherited method identity, and forbid the
application bootstrap's dependency namespace projection. No exceptions.

Python3.12 source tests use the existing third-party packages. Exact application
and dependency import locations are asserted; seven other externals are own
persistent worktrees at the application's recorded Git objects. The child used
for final product validation isee1e5438d64cb7d37e2641c2d9b3ee8870663adf;
later child receipt commits do not change tested production source.
Own native extensions were built normally with setup.py build_ext --inplace
(3.80s, peak203.67 MiB), not copied from installed packages.

* Dependency: eleven checks pass in4.42s, peak294.78 MiB. Includes three
  unchanged FileManager/persisted-workspace/pickle controls.
* Dependency-first application declaration journey: five pass in4.56s,
  peak260.05 MiB.
* Application-first declaration journey: five pass in4.56s, peak260.05 MiB.
* Independent custom application/dependency environment declarations: five pass
  in4.46s, peak260.23 MiB.

Each application journey writes real persisted metadata through the application
writer, constructs the workspace with its declaration, reopens through the real
FileManager, and launches a fresh native Python recipient of its pickle. Exact
source plane pixels, source axes, registry rebinding and bounded sample pixels /
source-shape provenance are checked. The declaration journey is not a substitute
for the still-unbound microscope registration path below.

Original and unresolved source failures
--------------------------------------

The exact original dependency-first negative control is reproduced unchanged:
one failed in4.35s, peak275.77 MiB, FileNotFoundError for polystore_metadata.json
after the application wrote openhcs_metadata.json. The first invocation's
missing-source-extension collection error is retained separately as a setup
failure. After the source contract change, the unchanged microscope test still
fails (one in3.26s, peak220.86 MiB) because its forbidden parent-owned constructor
does not yet bind the application owner. This is a real remaining source
integration requirement, not merely an installed/live gate.

Parent-only hunk, requested publicly at
https://github.com/OpenHCSDev/openhcs/issues/327#issuecomment-5923060449::

    from openhcs.core.virtual_workspace_metadata import METADATA_CONFIG

    backend = VirtualWorkspaceBackend(
        plate_root=Path(plate_path), metadata_config=METADATA_CONFIG
    )

Parent must apply this to its own _register_virtual_workspace_backend on PR206
and integrate the paired stack normally. I did not edit microscope_base.py,
test_microscope_handler_identity.py, benchmark/fragmented_roi_profile.py,
PR326 runtime/preparation files or any parent external directory. No original
test assertion is modified. The first authored application worker fixture
pre-imported arraybridge's installed source before activating pinned externals;
its two failures are preserved. The worker now faithfully imports dependency
metadata before the real application entrypoint, then other source owners.

Audit coverage and proof limits
-------------------------------

Archive entrypoint, pattern README, complete boundaries/implementation/over-time
references and both skills were read. Lightweight full-package AST census at
pinned heads completes without parse omissions: dependency12,209 code lines
in1.06s and application355,153 code lines in22.03s. These are syntax census,
not completed NRA ownership/native-equivalence proofs.

The unchanged original structural ratchet passes for final child source against
PR16: StringSubscript-2, other deltas zero. The first child draft's+2 failure is
retained, not waived. Actual tool SHA256 is
e323c94d49c2b72d9524a5169f123e64b4a6e46a41035ca9fb4497e49b6ca562.
Pinned tool package cannot import on3.12 (NameError: InputDocument); the existing
system3.14.7, matching original CI's3.14, executes its unchanged pinned local
Git source. This does not alter product3.12 validation or install/download
anything. Tool worktree: /home/ts/wt/metadata-namespace-327-audit-tool.

Semantic edits were hand-authored; no NRA transaction or completed R1/raw-record
certificate is claimed. Full NRA/R1 remains uncompleted, not waived. All raw
logs/XML/command bounds, including failures, are retained in
metadata_namespace_327_source_evidence.tgz. Initial census JSON filenames were
overwritten by the command-summary harness; the complete census stdout remains
in logs. Harness now uses distinct .command.json outputs. No science data is
part of this archive.

Acceptance boundary
-------------------

Parent must finish the forbidden registration hunk and rerun the unchanged
microscope workspace journey in both import orders. Then parent owns paired
merge/install and the actual affected installed native/MCP entrypoint, persisted
workspace reopen and exact pixel/provenance acceptance. No merge, activation,
installed-readiness or issue closure is claimed. No UI/MCP/scientific dataset,
science-runtime lock, Fiji/environment/interpreter download or installed-package
mutation occurred. Resource ownership/bounds are recorded separately in
metadata_namespace_327_resources.rst; terminal disposable scratch is archived
and cleaned by this owner.
