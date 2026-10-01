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
coordinate placement; the site-axis case exercises the same owner without a
channel special case. Reverse admission is not a claim of this checkpoint;
the existing fail-closed rematerialization guard remains. No consumer
dispatch/heuristics or mirrored rosters.
OneCPU/thread pools1,512MiB and60seconds per local shard. Installed frozen
Python supplies read-only dependencies, source imports come from this worktree.
Original failures and bounded R0/R1 outcomes are retained, never relabelled as
global or live acceptance. Full-context scans that cannot finish within these
bounds remain incomplete. Parent coordinates a distinct exact live slot later.

Status
------

Deleted the leaf's copied 18-line axis projection algorithm; its small hook now
delegates to ViewerComponentAxisSemantics.for_display_layout, also inherited by
NapariPendingLayerUpdate. SourceIdentityResolutionContext inherits the exact
workspace projection from SourcePatternResolutionContext; SourceBindingMatched-
ImageSet retains its one-position admission proof. ViewerComponentLayout derives
native STACK slots from mounted declarations, while each original display config
still owns grouping. NapariDimensionLayerState owns optional participation.
No new independent capability or registry is introduced: existing declaration
inheritance, registered handlers and polymorphic display work remain authoritative.
There is no artificial new mixin or replacement dispatch table.

Persisted formats changed: none. Numeric processing/CellProfiler interop changed:
none; no parity or performance claim. Source-authored bug repair, not a claim of
NRA-certified behavioural equivalence. Dependency binaries are read-only links
to the frozen installed environment, not newly built or installed artifacts.

Provider-free source results: 51 source-binding tests, 49 selected viewer/shared-
axis tests and 15 selected pipeline source-projection tests pass. The original
collection failure, two original defect failures and incomplete global audit
are retained under receipts/. Applicable committed R0/R1 gates are pending.
Draft PR351 is visible. No installed/native/MCP/UI acceptance or biology claim.
