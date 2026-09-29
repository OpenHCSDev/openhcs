# Custom source identity and compiled-inspection transport

## Source and ownership

This change is based on OpenHCS main
`90c755b76f680d5ff629cd483a73aeb48828daa1`. It was also applied to the
shared runtime at `2bc579ca9e5d3d70a130bec96ee6f001f3dd5c74` while preserving
unrelated dirty changes. It does not change scientific parameters or inputs.

The failing boundary was Python's standard pickle qualified-global lookup for
source-local measurement owners, enums, dataclasses and independent MI bases.
The existing custom-function source execution now owns their namespace. It
retains the actual execution globals and class/function identities rather than
building a helper catalogue, reconstructing classes, replacing the serializer,
or synthesizing creator frames. Imported declarations remain unchanged.

Source names and revisions belong to `CustomFunctionSource`; exact runtime
namespace identity belongs to `CustomFunctionSourceNamespace`. The canonical
callable retains that namespace and its declaration-validation operation.
`FunctionReference` and registry caches consult that operation. Persisted source
validation belongs to the existing manager and declared function lifetime.
Unchanged source reuse preserves the published owner. Changed, deleted and
renamed source revisions fail closed.

The independent review exposed an IDEN-6 publication race: a resolver could
cache a retired wrapper after lifecycle invalidation, including recreation with
identical bytes. The existing cache-publication lock now encloses revalidation
through the declaration owner. No second generation/source registry is added.

## Migration and evidence

The production change was applied through revision-checked NRA transactions:
one combined 28-stage trajectory followed by one declaration-targeted cache
publication correction. Supplied analysis-only sources were revision checked.
The live projected production bytes were compared with independently tested
isolated sources before application. Authored validation behavior is not a
native-equivalence proof. Preflight guard suites were empty.

The recorded global context contains 1,045 indexed OpenHCS files and eight
foundation contexts. Missing completeness/R1 fields in that audit limit its
coverage claim; this is not proof of zero architectural debt or detector gaps.

Final focused evidence after the cache-publication correction:

- 75 lifecycle/reference/callable-contract cases passed, including controlled
  concurrent recreate/replace/delete failures and fresh-current-owner controls.
- Five cold and five warm independent producer/consumer standard-pickle cases
  passed. They verify actual helper, enum, dataclass and independent MI identity,
  source isolation, ordinary inspection/reference contracts and stale rejection.
- Each integration shard was bounded to 60 seconds. No assertion was weakened
  to obtain a pass. Two existing pytest configuration warnings remain.
- Whitespace checks pass. One lifecycle-test import lint finding predates this
  change; no new finding was introduced.

The actual refreshed H002 UI consumed its compiled inspection successfully on
isolated display `:90`: bridge operation
`64f6f66d-43c0-43a5-9f0e-29e0085ed0ab`, compile artifact
`d853e8ba-69e0-4e30-b2a2-79750f1a35ef`, one callable invocation, 6.4 seconds
server time. UI state read back initialized/compiled/idle, not a scientific RUN.
That is live evidence for this inspection boundary, not installed-wheel,
spawned scientific worker, native installer or biological validation.

## Reproducibility and remaining limits

The six production files and two tests in this source checkpoint are the exact
reviewed implementation. Existing decision recipes, failed-before evidence,
XML reports and live receipts are retained under
`/tmp/openhcs-source-owner-audit-0xiatDLq` and
`/tmp/openhcs-live-source-cutover-Cu6AqTQO`. The evolving blind-analysis handoff is
`mcp_outputs/blind_skill_resume_20260928.md` in the shared checkout.

At this checkpoint, the transport fix has not been pushed or merged. Hosted CI,
a fresh installed wheel and biological H002 acceptance are not established.
The stale client-owned stdio MCP is not a valid test endpoint; fresh resident
public MCP and live UI validation are separate evidence. The public call-boundary
performance timeout remains unresolved and was not padded to hide it.
