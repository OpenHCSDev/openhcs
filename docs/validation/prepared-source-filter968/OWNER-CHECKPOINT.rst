Prepared workspace source-filter admission: contribution to #968
================================================================

Dewey owns integration and installed acceptance. The initial sections below are
historical investigation, superseded by the implemented checkpoint at the end.
Singer contributes the source
correction in this branch. Base is main2945688c4; no scientific request is
replayed and no active package, plate metadata or author client is modified.

Determining source relationship
------------------------------

MicroscopeSourceSelectionRole.PREPARED_WORKSPACE preserves the prepared handler
when create_microscope_handler receives new source bindings. This preservation
is legitimate: replacing the handler with raw-file ingestion can discard the
persisted source reference/provenance contract. OpenHCSMicroscopeHandler then
initializes the persisted main directory without consuming source declarations.
Orchestrator.source_workspace_projection obtains the entire persisted projection
from VirtualWorkspaceSourceProjectionAuthority, also without those declarations.
SourceBindingWorkspaceProjector.source_candidates and
projection_set_for_candidates already own declared path-filter admission.
The fix must bring retained candidates through that existing admission owner;
it must not introduce another filename matcher or rewrite acquisition metadata.

Retained original execution87ce42df-e3a5-4662-a5ee-0b9104cc6804 selected nine sites
despite the declared filename clause in REPAIR01-site7.py. The original inputs,
settings, outputs and terminal receipt remain immutable. Issue968 carries their
exact paths. This is a source-universe mismatch, not scientific accuracy proof.

Ownership coordination and implementation boundary
-------------------------------------------------

Requested exact shared-file/hunk release from Dewey before production edits.
PR973ea48dd982 changes runtime input consumption, not workspace candidate admission.
PR96460973129a changes compiled retention/runtime queries. PR966723d22cd changes
completed publication and DOES touch source_workspace_projection.py; that hunk
requires direct integration coordination. Neither PR is treated as the filter fix.
No shared production file has been edited in this checkpoint.

NRA/refactor-audit and the catalog README were reread. Relevant ownership leads
are BOUND-2 (bypassing the existing admission owner), IMPL-12 (avoid a copied
filter procedure), and AGENT-2 (migrate the retained route, not only fresh input).
The existing refactor-audit Repository/Package loader parsed all702 production
modules at2945688c4 with zero parse omissions. An AST declaration/name/attribute
query enumerated the projector/filter/factory/projection family across handler,
orchestrator, compilation session/compiler, runtime context/function runtime,
execution-session/inspection services, inventory, viewer source and CP export.
The query also identified unrelated measurement_feature_queries.source_candidates
names; these are not workspace admission consumers. Relevant dependency/MRO
semantic closure remains pending, not silently omitted or claimed as global proof.

The factory passes source_bindings_config to MicroscopeHandler.create, whose
base implementation discards it; the prepared handler inherits that method.
VirtualWorkspaceSourceProjectionAuthority.from_context and from_plate_metadata
also receive no source declarations. This confirms the bypass family rather
than a failure of SourceBindingsConfig.source_path_filters_match itself.

Acceptance and remaining work
-----------------------------

After the coherent owner correction: selected, unfiltered and no-match retained
workspace controls, two-channel exact source references/provenance, and a new
declaration admitted without generic consumer edits. Then ordinary installed
inspect/compile/execute in an engineering destination with the selected domain
and exact outputs. These are pending, not passed. No timeout or scope guard is
weakened. No new environment, worktree or scientific run is needed.

Checkout custody
----------------

Reused the finished UI checkout through its original persistent path. Dalton's
cold relocation remains intact. Eight foreign gitlinks, historical validation
deletions/symlink targets and untracked originals remain unchanged. Only this
new receipt is staged; no reset, cleanup, bulk add or foreign edit.

Implemented and source-qualified checkpoint (2026-10-06)
-------------------------------------------------------

Dewey released candidate admission, prepared create/initialize, orchestrator,
from_plate_metadata and subsequent from_context declaration plumbing. The five
production files are source_binding_workspace.py, source_workspace_projection.py,
microscope_base.py, microscopes/openhcs.py and orchestrator/orchestrator.py.
SourceBindingWorkspaceProjector admits retained references using the original
SourceBindingsConfig matcher and SourceMetadataFields.source_filter_paths.
Empty/absent filter-path identities retain the existing backend/path fallback;
no new absence policy or reserved-field decoder is introduced.

MicroscopeHandler.source_admission_config is the nominal handler hook; the
prepared handler retains its original resolved declaration and supplies it.
The existing authority consumes it on both plate and runtime-context paths.
Orchestrator selects the admitted component domain, then applies its original
common component filter. No second filtering procedure, registry, matcher or
acquisition metadata rewrite remains. The prepared handler protection remains.

Mainc882d5edc67bffe7ec7f2eb3a2eeb7fe64e9415a is integrated in the two-parent
merge bdf5c6a3c410e1a49260d1bb72cfc103d9a4a876. The #966 runtime authority
and completed-output overlay are preserved: raw source admission occurs before
completed outputs are overlaid, not as a filter on produced filenames.
Normal porcelain merge refused the pre-existing validation symlink/deletions
before mutation (stash failed). Git merge-tree/read-tree/commit-tree integrated
the actual merge with both parents; the validation tree diff was empty. No
stash, reset, history restoration or foreign gitlink edit was performed.

The original AST census parsed 702 production modules with zero omissions.
Relevant declarations/consumers were read through source metadata, projector,
handler factory/MRO, orchestrator and runtime authority. BOUND-2 and IMPL-12
review corrections remove the reserved-field decode copy and duplicate filter
procedure. This is family source evidence, not global NRA/dynamic proof.

qualification05: 65 PASS, terminal0, pytest10.00s/wall11.57s, peak350384KiB,
swaps0. Both source-binding workspace and completed-output lifecycle files run
through the original source bootstrap with byte-matched native extensions and
read-only target25 dependencies. No package installation/native/UI launch.
The controls exercise actual prepared handler, ProcessingContext and
PipelineOrchestrator: selected site7/two channels, unfiltered18 references,
independent site3 declaration, site99 no-match, original provenance object
identity, unchanged serialized metadata, component-filter intersection and
completed-output overlay outside the raw filename clause.

Original qualification01 collection failure (stale PolyStore API) and
qualification02 fixture identity failures remain byte-exact. The fixture now
declares its filename metadata explicitly; no matching assertions were waived.
qualification03/04 passed the focused controls; qualification05 is the integrated
batch. qualification-logs.tar.gz contains all original stdout/stderr, including
the failures. Loose pytest scratch remains uncommitted and is not a new authority.

Remaining acceptance belongs to Dewey: ordinary whole-candidate installed
inspect/compile/execute for selected, unfiltered and no-match prepared input.
Use the existing test fixture's nine-site/two-channel explicit metadata rules;
assert selected site7 yields two source references and exact two-channel
provenance, unfiltered yields18, no-match refuses before execution. Verify the
compiled/executed domain and exact persisted outputs through public routes,
then close the original engineering handles. No scientific request is replayed.
