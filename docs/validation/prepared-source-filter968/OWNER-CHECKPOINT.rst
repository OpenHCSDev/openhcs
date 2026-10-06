Prepared workspace source-filter admission: contribution to #968
================================================================

Dewey owns integration and installed acceptance. Singer contributes the source
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
Complete relevant production/dependency AST closure and semantic read precede
the correction; no global dynamic proof is claimed by these source observations.

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
