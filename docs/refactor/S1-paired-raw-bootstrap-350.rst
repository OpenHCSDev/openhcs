Paired raw review ownership repair (issue350)
===========================================

Integration owner: Schrodinger. Release/live owner: parent.
Audited main094425c8c81324da7a3878379074e1bd8234ff52.
Branchfix/paired-raw-bootstrap-20261001. Rules:00-RULES.md.

Diagnosis and target
--------------------

IDEN-3/IDEN-6: SourceBindingMatchedImageSet.members_for_binding unions
workspace keys and source-universe paths before exact identity matching.
A declared workspace position and its physical address become two positions.
SourcePatternResolutionContext owns the declaration mapping; extend its exact
position projection, inherited by SourceIdentityResolutionContext. A physical
address expands to every explicitly declared position, not to a basename guess.
Distinct planes/virtual positions on one store remain distinct; retain exact
component metadata matching and the one-position rejection.

IDEN-7/BOUND-2: NapariLayerDisplayPipeline.display_layer_batch previews the
shared domain using only incoming display_config STACK axes. Existing raw
routes still require channel, omitted by a LAYER incoming config.
ViewerComponentLayout owns mode/order; ViewerRouteComponentValueTracker owns
domains; ViewerComponentAxisSemantics owns the independent domain/layout
capabilities. Derive shared display slots from participating declarations,
without changing route grouping or maintaining a second axis registry.
Generic display consumers use those original owners; no channel special case.
Preserve exact route coordinate placement and fail-closed ambiguity/expansion.

Scope and exclusions
--------------------

Source positions and viewer component projection only. No numerical algorithm,
external persisted format, source TIFF, scientific parameter or installed
package change. Runtime derived views only; no compatibility reader or fallback.
PR349 dev-client action/command/core/rendering files and its tests are parent-
owned and excluded. No validation.lock, native/MCP/UI launch or live claim.
Scientific trial remains terminal/read-only; use synthetic engineering fixtures.

Proofs and gates
----------------

One family-level canonical source identity test, equivalent spellings and
distinct-position negative cases. A mixed STACK/LAYER production display test
using the existing native ViewerModel proves both channel identities and exact
coordinate placement; reverse admission and other component axes exercise the
same owner. No consumer dispatch/heuristics or mirrored rosters.
OneCPU/thread pools1,512MiB and60seconds per local shard. Installed frozen
Python supplies read-only dependencies, source imports come from this worktree.
Original failures and bounded R0/R1 outcomes are retained, never relabelled as
global or live acceptance. Full-context scans that cannot finish within these
bounds remain incomplete. Parent coordinates a distinct exact live slot later.

Status
------

Diagnosis established from source and immutable engineering repro receipts.
Implementation/tests and applicable R0/R1 are in progress. Draft publication
does not mean accepted installed/native/viewer behaviour or biological accuracy.
