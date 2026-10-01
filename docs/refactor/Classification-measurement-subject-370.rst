ClassifyObjects measurement subject (#370)
=========================================

Owner and boundary
------------------

Independent source sidecar:
``/home/ts/wt/openhcs-classification-measurement-subject-20261001``, based on
main ``bcf5fa55a21d33126d0ca2c2e100c85e4f985960`` (merged PR365).
At initial qualification PR367 was awaiting parent-installed acceptance; it
has since merged at be5eabcfcf9b9ef223304280aad6929a60eba8c5 after the parent's
bounded engineering named-selector journey passed. That acceptance does not
qualify this independent classification change.
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
Applicable implementation, membership, identity and boundary patterns were
reviewed explicitly: IMPL-1/3 reject consumer string/type dispatch; IMPL-4
rejects a half-finished family repaired only for one leaf; IMPL-12/13 reject
copied procedures and a second mechanism with different rigor. MEMB-1/2 reject
rosters restating the original declaration family or capability; BOUND-2
rejects bypassing the existing typed relation owner. IDEN-1 keeps dependency
provenance, measured object identity and row-recording policy as distinct
facts. The old algorithm is deleted from the input-policy owner in place;
there is no parallel implementation or compatibility forwarder. Real
independent MI and cooperative super() extend the original owning ancestor.

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
Final reviewed source checkpoint:
``a5a0972e481d9e5062aef8e9126806c356f25551``. The complete declaration,
provider and new subject suites pass together: 76 passed, 7.85s,
383.39MiB combined RSS, no deselection. This includes original object/image
measurement relations, producer selection and source-provenance negatives.
Pinned original R0 against main bcf5fa55 passes in 15.07s / 85.25MiB:
5161 measured entries, increased=[] and decreased=[]. The tool is the
readonly ``comms-ratchet-pinned-ui348-20261001/src`` with actual Python3.14
and readonly metaclass backing, not a copied detector. Ruff F checks on
touched production/tests and I checks on the new test, plus diff-check, pass.

No generic consumers or original tests changed. The initial handoff/evidence
commit changed documentation only; the later cooperative proof below extends
only the new test and receipt. Exact commands and full output, including
the original red and initial fixture red, are archived with this document.
This qualifies the real source declaration -> contract -> generic compile
boundary, not installed classification execution or numerical correctness.
Parent-installed acceptance remains the only remaining acceptance boundary.

Tracked archive:
``docs/refactor/receipts/classification-measurement-subject-370-source-20261001.tar.gz``
SHA256: ``95aaa8e25c2f35cee817a3391f194733c39d66a74903e19c3f4440304c297c01``.

Cooperative-hook review correction
----------------------------------

Reviewed head 364090ae5 against current NRA and authoritative refactor-audit
archive, including IMPL-1/3/4/12/13, MEMB-1/2 and BOUND-2. No production
ownership violation found. The proof gap was narrower: the new declaration
test did not assert that a newly composed hook retained all inherited
contributions. Inheritance assertions alone would not detect dropping super().

The test-only StackMeasurementOutputCapability extends the original
CellProfilerModule relation hook through cooperative super(). It selects an
exact stack using the original SettingToKeywordBinding and artifact-name
projection, then appends the original typed SourceStackLineageSourceRelation.
StackSubjectCapabilityProbe contributes only its own names and concrete
setting binding, composing that capability with ObjectSubjectCapabilityProbe.
No shared consumer or production declaration is edited for the new case.

The actual shared measurement_output_artifact call must retain, in order,
all generic dependencies and group-domain relations, the inherited exact
object subject, and the new exact stack-source relation. An unselected image
comes first, so first-input selection cannot pass. Original native declaration
validation accepts the result; the independent recording hook still suppresses
table-level object ownership. The original new-leaf case also now asserts
both inherited provenance and subject relations, not merely class/MRO identity.

All three complete source suites: 77 passed, 44.54s supervisor wall,
383.20MiB combined RSS, no omission or deselection. CPU0, one-thread pools,
512MiB / 60s and the native-child guard remain unchanged. Ruff F/I and diff
checks pass. No further native, installation, provider or scientific run.
Production bytes remain identical to a5a097 (git diff --exit-code -- openhcs),
so the parent's private installed 371+372 pair needs no rebuild. Its acceptance
is still separate and parent-owned. Original pinned R0 applies to those same
unchanged production bytes; no new R0 or global FULL claim is made.

Exact new-test SHA256:
``ea81a9a03ec20c6040707978b1ce6c828ea9d7b67561cf2275d57f44165722d7``.
Supplemental archive:
``docs/refactor/receipts/classification-370-cooperative-hook-review-20261001.tar.gz``.
The original failure archive above is unchanged.
