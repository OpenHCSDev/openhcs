Select mounted producer-bearing routes for viewer retirement
===========================================================

Source checkpoint: main01044edbc13c9a234a7ec52f772acca8015ccc99,
2026-10-04. Singer owns this narrow viewer-guide correction. Current open522
retirement/selection and Planck's independent point-highlight investigation
are coordinated; open697 final summaries and693 analytical colour rendering
are disjoint. No production, dependency, runtime or scientific files change.

Determining relation
-------------------

Viewer state deliberately includes declared routes without a mounted layer.
NapariViewerProjectionABC.route_keys unions route titles and component groups;
layer_state_for projects mounted from the actual layer and producer_identities
from the original NapariComponentGroupStore.producer_identities_for. An
unmounted, zero-item route can correctly have an empty producer array.

ViewerLayerRetirementControlOptions rejects empty producer tuples before
dispatch. Native NapariComponentAwareDisplayCoordinator.retire_layers also
requires every selected route to be mounted and its exact producer set to
match before any removal. This protects whole-set atomic admission, not a
ban on null invocation_key. Original PolyStore StreamProducerIdentity declares
invocation_key optional and its from_payload decoder preserves None; the
request annotation delegates to that decoder through BeforeValidator.

The retained refused request selected eleven routes: eight populated producer
arrays plus three empty arrays. Original readback marks those three unmounted
and zero-item. The generic error is consistent with the empty-set guard, not
evidence that a null invocation_key or a valid mounted producer is rejected.
The original request, error and subsequent scene remain untouched. No replay
or author feedback occurs. No unsupported retirement fallback is introduced.

Owner and change
----------------

The declared manifest source for openhcs_viewer_qa is the existing packaged
references/viewer-qa.md; this guide has no RST backer. Its retirement procedure
now explicitly chooses mounted entries with nonempty returned producer arrays,
omits unmounted placeholders, and preserves null optional identity fields.
The declaration/decoder/coordinator remain the same owners; no copied identity
codec, route selector, store, registry, guard or alternate guide is added.

Applicable review: BOUND-2 (use the existing producer decoder), IDEN-7 (a
declared route is not necessarily a mounted layer), and IDEN-6 (exact route and
producer incarnation, not title or port). Skill-creator limits this to the
missing operational distinction; Diataxis keeps it in the existing how-to
step, rather than creating a protocol reference or a new universal gate.

Qualification checkpoint
------------------------

Offline actual SDK/request-chain acceptance and ordinary knowledge projection,
packaged guide availability and managed-sync checks are pending. The former
will decode the original saved values without dispatching a mutation; the
latter will expose the same canonical bytes in disposable owned test roots.
This documentation change does not claim a new native retirement, selected
geometry-survivor acceptance, autonomous gain or installed scientific update.
Existing active/frozen author packages remain unchanged. CI deferred.
