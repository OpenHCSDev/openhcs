ClassifyObjects measurement subject (#370)
=========================================

Owner and boundary
------------------

Independent source sidecar:
``/home/ts/wt/openhcs-classification-measurement-subject-20261001``, based on
main ``bcf5fa55a21d33126d0ca2c2e100c85e4f985960`` (merged PR365).
PR367 remains at its reviewed checkpoint for parent-installed acceptance.
PR362 and Lorentz #368 claims were checked; this patch does not touch their
files, function_patterns, invocation providers, runtime edges or numerical code.

Original failure retained
-------------------------

The original, unmodified
``test_classification_rules_remain_public_while_declaring_prior_measurements``
failed at ``compile_function_pattern``: the ClassifyObjects measurement output
has ordinary provenance but no typed measurement subject. Against exact main,
the complete original provider suite produced 25 passed / 1 failed in 6.68s,
383.36MiB combined RSS. The original receipt and log remain at
``validation/original-main-provider.{json,log}``. Earlier PR367 baseline
receipts remain untouched. Neither failure is a waived acceptance.

Owning implementation
---------------------

The existing ObjectMeasurementInputModule bundled two independent policies:
object-subject output relations and measurement-specific input settings /
invocation splitting. The existing algorithm is moved, not copied, into
ObjectMeasurementArtifactOutputModule, a behavior-owning ancestor extending
MeasurementArtifactOutputModule. ObjectMeasurementInputModule now inherits
that capability together with ObjectArtifactInputModule; its binding and
splitting implementations are unchanged.

ClassifyObjectsSingleMeasurementModule composes the same output capability
with its existing input, prior-measurement and recording capabilities.
Cooperative super() retains all original provenance/group relations before
adding exact object-subject relations. Both declared function variants inherit
the fix. No leaf override, consumer name/type switch, registry, fallback or
facade is added. Runtime recording still suppresses a table-level object name;
that independent policy does not erase the declared measured object identity.

Pattern review
--------------

Current NRA/refactor-audit skills and the current NRA skill archive were read.
Applicable implementation, membership and boundary patterns were reviewed:
IMPL-4/12/13 (one shared algorithm, behavior-owning inherited capability,
cooperative independent MI), MEMB-1/2 (original declarations/registry remain
the authority), and BOUND-2 (typed subject identity, not ordinary dependency
provenance). The old algorithm is deleted from the input-policy owner in place;
there is no parallel implementation or compatibility forwarder.

A new ObjectSubjectCapabilityProbe declaration uses only its own module /
callable names and the existing capabilities. The original CellProfilerModule
registry discovers it, the original generic output mechanism derives its
object subject, and no generic consumer is edited. Tests prove shared method
identity and MRO ordering, retained recording policy, and no inherited
measurement-input setting/splitting policy for classification.

Focused source qualification
----------------------------

The unchanged complete provider suite plus eight new behavioral cases passes:
34 passed in 6.47s / 377.82MiB combined RSS. Both classification variants,
retained prior dependencies, new declaration discovery, cooperative MRO,
missing subject and ambiguous subject rejection are covered. The initial new
fixture used the wrong ModuleBlock constructor; that red receipt is retained,
and only the fixture was corrected to the actual original constructor.

All checks use CPU0, one-thread pools, a 512MiB combined RSS / 60s supervisor,
the readonly parent dependency interpreter and explicit own source. A
source-only subprocess guard rejects native child launches. No native,
scientific, GUI/MCP, provider, installation or heavyweight gate was run.
Broader source declaration regression and pinned R0 qualification follow;
actual installed acceptance remains parent-owned and is not claimed here.
