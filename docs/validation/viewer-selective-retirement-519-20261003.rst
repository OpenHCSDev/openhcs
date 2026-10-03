Selective managed-viewer retirement519: original-owner source checkpoint
======================================================================

Scope and custody
-----------------

Current implementation checkpoint (2026-10-03)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Parent released the native coordinator/reconciliation, original route-state/
settlement/batch/display-work hooks and typed protocol/request/gateway/service/
capability family. Singer implements on the existing522 branch. Root394 core
producer, persistence and materialization remain untouched. Current Root claim
checked at0fe0482d2784bd6ab1d3a7b3fbb6e5ddfb473e55; no other selective-retirement
implementation is published. The original investigation below and its source
archive remain historical evidence, not the implementation qualification.

The coordinator now owns one purge recipe used by native-deleted reconciliation,
unmounted clear-state cleanup and explicit typed retirement. Route state stops
its timer and releases retired terminal settlement items; each original store
releases its route entry. Known failed terminal settlements are eligible, while
pending/accepted intake, active settlement and deferred display work are refused.
The entire explicitly requested producer identity set is compared by exact typed
equality before mutation, including invocation identity; no hidden-layer/name/
candidate-age policy decides disposal. Existing source/result files are not read,
changed or deleted by retirement.

Survivor pruning uses the existing registered display/rematerialization traversal.
The display ancestor preserves common native presentation; the independent image
presentation capability cooperates through super() to preserve intensity/gamma/
colormap/interpolation. A rematerialization request's small publication hook leaves
peer traversal with its original owner instead of recursively re-deciding domains.
The existing request ancestor now carries the operation deadline shared by snapshot
and retirement; the snapshot-specific copy is deleted. The new capability is
discovered by the existing generated MCP binding, with no server/context roster
edit. A CLI leaf supplies the exact producer mapping through the same request.

Qualification is pending at this first implementation checkpoint. Source controls
exercise real Qt scheduling and ViewerModel, typed queue/gateway/service, payload
release, exact stale-incarnation refusal, terminal-failure retirement and independent
cooperative capability hooks. No installed/live/RSS-reduction claim is made. There
is no new runtime/client/viewer launch, package installation or scientific contact.
Unexpected native removal/rematerialization errors are not an atomic rollback;
their failed operation disposition must not be replayed as if nothing happened.

Original investigation checkpoint
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Singer owns this source investigation under the parent's explicit assignment;
parent retains302/308 mounted-route integration and later installed/native
acceptance. This checkpoint contains source evidence and a narrow integration
proposal, NOT a working retirement implementation or proved memory leak.
No viewer/native/MCP/client launch, installation, scientific input or author
contact occurred. Existing503 branch/evidence and foreign gitlinks remain intact.
The same finished checkout now has a new branch from merged main, with no new
worktree/environment/dependencies. No production source has been edited.

Claims checked before source work
--------------------------------

Audited main f7de9efad393bce83a3756a271f0cd4383783ea9 (merged503); current
Root394 4c636a281de4da7341f4f9f6bb8f718c75644a1d;494
7a067c505444ec7d8720da21118dc85787129c59.519 is OPEN/unassigned with no
implementation comments. All11 current open PR titles/heads listed; relevant
owner bodies/file rosters checked: no published selective-retirement implementation. Search519 across
all PR states returns only merged guide520.519/302/308 explicitly name parent
integration;494 remains point-projection receiving and Root394 remains runtime/
materialization integration. Runtime/viewer, agent viewer DTO/service/capability,
MCP binder/CLI and orthogonal consumer files in the selected family are BYTE
EQUAL main to current Root394. Root's separate core producer/source deltas are
recorded, not claimed equal or taken over.468 touches tracking, not this seam.
Legacy agent-comms registry has no current running OpenHCS claim; direct parent
assignment and current GitHub owner records determine this task's ownership.

Determining owners and consumers
-------------------------------

* napari_viewer_server.py:943, NapariComponentAwareDisplayCoordinator owns routed
  intake and existing deleted-native-layer reconciliation.1037..1039 currently
  purge route state, item groups and declared/observed component domains. Reuse
  this owner; do not copy three purges into a new action or change hiding.
* napari_streaming_handlers.py:1506, NapariLayerRouteStateStore owns mounted
  layers/titles/dimensions/pending updates/errors and settlement. purge_route
  removes dictionary entries but does not itself stop a pending timer. Original
  cancel_pending_update/drain_pending_updates/reset_settlement own cancellation
  and terminal-release rules; running settlement cannot be silently reset.
* NapariLayerSettlementState:291 owns the tuple of original pending updates,
  each with source items. Completed progress retains that tuple until the
  original reset_settlement boundary. Purging mounted stores alone therefore
  does not prove all retired payload references released. This is source
  retention evidence, not an attribution of either reported OOM.
* NapariLayerDisplayPipeline:2148 owns per-route deferred work and shared-axis
  projection/rematerialization. Its scheduling/completion methods own timer and
  continuation identity. Existing rematerialize=True and nominal display
  handlers already support pruning; no second painter/display loop is needed.
* NapariBatchProcessorStore:1794 owns lazy route processors. Read actual
  PolyStore NapariBatchProcessor: it holds its server, NOT an accumulated image
  list/timer. Retire its route entry for lifecycle completeness, but do not
  misidentify it as a separate scientific-array cache.
* ViewerRouteComponentValueTracker:1104 owns per-route domains; shared_values_for
  derives their union. Retire only selected domains and reproject survivors
  through the existing pipeline. Preserve survivor source items/metadata and
  physical scale; aggregate display arrays may legitimately rematerialize.
* Native viewer.layers.remove uses Napari LayerList deletion, ViewerModel event
  disconnection and VispyCanvas._remove_layer/VispyBaseLayer.close. The latter
  disconnects layer/camera events, closes the visual and deletes its scene-map
  entry. Invoke this external lifecycle, not private GL deletion or broad clear.
  Result-selection callbacks already use weak layer references/weak-key stores;
  no strong mirror or new callback registry is warranted.
* NapariControlMessageAction's registered family/accepted Qt reply queue owns
  action dispatch. NapariMountedRouteControlMessageAction owns exact mounted
  route resolution. New retirement action is a small member delegating lifecycle
  work to the coordinator; no central viewer/type/origin switch.
* ViewerWindowControlRequest, ViewerWindowGatewayABC/ZMQViewerWindowGateway and
  ViewerWindowService own request/deadline/transport/result boundaries. Existing
  OperationDeadline and accepted-operation semantics must prevent late mutation
  after a caller's deadline, without increasing any timeout or adding timers.
* AgentCapabilityDeclaration + AgentViewerWindowRequestServiceInvocation and
  GeneratedMcpViewerRequestToolBinding already generate tools from declaration
  input fields. Add a typed request/result and capability member there; generic
  MCP server/context dispatch need no retirement branch/roster. An optional
  ordinary CLI CommandSpec is its own leaf, not an alternate API/registry.

Required relation and exact next shared hunk
------------------------------------------

Explicit caller-selected exact mounted route identities are retirement targets.
Hidden is not retired, and neither names, counts nor producer origin imply that
a route is disposable. Reuse full StreamProducerIdentity and existing source/
domain records for preconditions, not a second generation/receipt store. The
route key itself is insufficient as a generation witness: route_parts omits
invocation_key, while the original typed producer carries it. Before mutation,
resolve/validate the ENTIRE selected set, the exact current identity and the
original settlement/intake disposition. Missing/stale/foreign/pending/failed or
UNKNOWN work must yield an explicit non-success without collateral retirement.

The coordinator's one retirement recipe must release the selected native layer,
route/group/domain, per-route deferred work and batch entry through those
existing owners. Retain raw/current/needed-reference routes and durable source/
output files. Release completed settlement references through its existing
terminal reset, never by cancelling unknown work or deleting history. Keep
survivor semantic coordinates, calibration, contrast/camera/selection correct
through original rematerialization/selection hooks, not by freezing stale axis
indices or inventing an aggregate domain. Do not automatically guess old
candidate routes from visibility; the supported MCP operation performs the
selected retirement at a safe settled boundary.

Shared production hunk to coordinate with parent302/308 before editing:
napari_viewer_server.py coordinator deleted-route reconciliation + display-work/
registered action methods; napari_streaming_handlers.py route-state/settlement/
batch-entry release hooks; viewer_component_system.py only if the ORIGINAL
domain owner needs a narrow hook. Receiving declarations go in viewer_controls,
OpenHCS-owned viewer_protocol message family, agent/dto/viewer, viewer service/
gateway and capability leaf. Do not change Root394 core/persistence/materializers,
frozen installed sources or extracted dependency gitlinks. Delete replaced purge
duplication at existing reconciliation/clear consumers in the same coherent
change; preserve clear's302 mounted-inventory behavior.

Automatic after-settlement dispatch must compose with the existing settlement
owner and control deadline. Exact terminal/pending-intake admission remains to
be implemented and exercised; this source checkpoint does not supply a second
poller, timeout engine or pre-authorized destructive policy. Parent's shared
coordinator hunk disposition is the next integration dependency, not a new
unclaimed-owner queue. No production patch or runtime is submitted here.

Source evidence and proof limits
-------------------------------

Read latest NRA skill and authoritative nominal-refactor-advisor/skills/
refactor-audit.skill SKILL/catalog README plus full identity, membership,
implementation, boundaries and over-time pattern files. Applicable patterns:
IDEN-1/6 (route versus generation/visibility), BOUND-2/8 (typed source/domain/
producer facts across request/reply), IMPL-12/13 (copied purge/settlement loops),
MEMB-1/2 (parallel tool/route rosters), TIME-9 (alternate codec/compatibility).
Existing behavior-owning classes and shared registered ABCs remain load bearing;
compose genuinely independent hooks with cooperative MRO only where they do work,
not an ornamental inheritance layer.

Thin source caller uses original audit ParsedModule/FunctionFacts/Repository,
not a copied detector; no product import. Complete704 production +668 tests +188
first-boundary dependencies parsed, zero errors. Named projection38 production/
34 test modules; dependency-detail shard records ALL188 modules' declarations,
imports and function facts. Scene shard additionally records ALL245 Napari Qt/
Vispy modules, zero errors. External compiled Qt/GL behavior is not executed or
proved by AST; dynamically connected native events were read semantically.
No full NRA-detector/global ratchet or runtime acceptance is claimed.

Original source-family01 was terminal2 before script start because systemd's
working directory was /home/ts; its stderr remains unchanged. Corrected02 used
explicit original WorkingDirectory:21.435s,77.2MiB peak,Swap0,terminal0.
Independent dependency/scene shards:1.927s/16.9MiB and1.814s/18.4MiB,Swap0,
terminal0. Each kernel bound CPU1/512MiB/noSwap/60s, no widened limit.
Critical disk/swap advisory preserved; cheap snapshot had11.5GiB available RAM.
Static JSON records/commands/raw logs are archived; no tests run on this turn.

Acceptance to implement, then verify last
----------------------------------------

Use existing real Qt/ViewerModel reset-transition fixture (no renderer clone):
raw + two completed candidate routes + needed reference, exact selected retire,
survivor source-item/domain/scale/semantic-coordinate/presentation proof. Include
interior shared-axis prune/rematerialization, RGB + Shapes + Points, missing/
stale/foreign route, queued replacement, partial Shapes, failed/active settlement,
deadline and no resurrection/duplicate reply. Prove retired object/array weak
references released without requiring allocator RSS to fall immediately.
Independent new handler/capability declaration must exercise real hooks through
the generic coordinator/binder without generic consumer edits; inheritance
assertions alone do not satisfy this control. After the source batch, parent
qualifies ordinary installed public state/payload/matched captures and measures
route-owned references/RSS/PSS under separately released engineering custody.

C39's111 mounted layers and R001094's reported4.5GiB OOM/239 pending soma reopen
are retained correlation witnesses, not leak/layer-count causation. R0010 caller
143/UNKNOWN execution/no public close receipt must remain that disposition.
P001 candidate01 settlement error belongs existing308; its independent authored
candidate02 reopen is not replayed or declared fixed by this investigation.
No scientific pixel/reference/answer files were read or copied into this PR.

Byte-exact source evidence archive
---------------------------------

``viewer-selective-retirement-519-source-20261003.tar.gz``, nine members,
469035bytes, SHA256
``f3b76a5c7eebd0c5732957fb7ca646d0fef697ca1ec3711e2179ddcdb81a7bd8``.
Original-file tar comparison passed. The original caller's symbol projection
preceded the later dependency/scene-detail options; its emitted records retain
that original selection, and current source caller/options are archived as such.
No original first failure or prior503 source/evidence is overwritten.
