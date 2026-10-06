Funded sealed reader terminal cutover
====================================

Publisher690 correctly removes the numeric PSI threshold for new declarations
and guards. Its unconditional shared-field deletion breaks still-funded sealed
predecessors: their original resource-check.sh line143 requires the original
canonical FUND value before every action. Current four immutable run owners
still declare that contract. They must remain byte-identical and operational.

The existing expected-revision publisher already resolves every funded member
through its immutable run owner. That loop now derives the retained reader
contract from those same declarations, retaining only the existing canonical
field while a funded predecessor declares it. A new declaration cannot set it;
successor-program.jq still deletes it and the new guard never reads/enforces it.
After the last predecessor's exact terminal retirement, that same publication
automatically removes the field. No secondary roster, clock, version switch,
compatibility guard, new authority or PID inference is introduced.

This narrowly preserves an explicitly requested immutable external-to-the-new-
family reader contract, rather than reintroducing the removed numerical policy.
Ownership follows the existing FUND membership and physical run declarations;
no current scientific source, instructions, package or frozen operations change.
Pattern leads IDEN-7 and AGENT-7: global deletion must not invalidate genuine
continuing-reader custody or create an approval queue.

Coverage: original publication/prepare/retirement, slot projection, resource
reader and controlled shell consumers semantically inspected. Existing audit
overlay targets the complete operations root: zero Python modules; Bash/JQ
are explicitly outside Python AST proof. Shell syntax, original-family controls
and actual canonical receiving/admission are the behavioral acceptance.

Qualification: original test_funded_programme_publication.sh publication01
terminal0 confirms old field100 retained, new run field absent, final reader
retirement removes it, expected revision/no replay, exact controlled recorder
child42 and untouched journals. Original test_operation_resource_admission.sh
resource01 terminal0 preserves real desktop/custody/deadline failures while
high PSI4.82/1.09/.23 remains observational, never a new numeric veto.
Persistent logs are engineering-active-reader-cutover-20261004-{publication01,
resource01}.log under the existing issue-batch; no native or provider launched.
