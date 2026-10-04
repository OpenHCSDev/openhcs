Prepared callable signatures and raw argument admission
======================================================

Registered argument contracts belong in function-library warmup before server
readiness. Newly authored declarations prepare before compiler validation and
resolve once per compilation. Invocation must consume those prepared contracts.
This is a correctness/preparation dependency of the plumbing work, not a claim
that signature caching alone removes multiple seconds.

CallableMetadata carries the resolved canonical inspect.Signature. Parameter
names, annotations, defaults and semantic controls derive from that declaration.
Preparation publishes it only after every registered preparation hook finishes.
FunctionReference and existing namespace/pickle/cloudpickle transport retain it.
The compiler reuses registered snapshots and captures fresh authored snapshots;
the old late invocation preparation is removed.

Actual boundary inspection found that most CP raw targets differ from their
semantic signatures because injected controls are absent from the raw function.
The existing metadata owner therefore also carries a raw-runtime Signature only
when required by that distinct boundary. Identical boundaries reuse canonical;
default objects are retained by identity and never compared through value equality.
Existing invocation and batch-request owners receive the exact raw view for
filtering/defaults. Three independent signature/default/type LRUs and the obsolete
signature-parameter helper are removed. Unprepared authoring and distinct generic
wrapper queries remain live. Explicit library rewarm or supported declaration
invalidation refreshes registered snapshots; arbitrary direct annotation/default
mutation does not retroactively rewrite compiled contracts.

Raw array admission is derived from the callable's declared nominal type, including
unions and Annotated. The adapter retains context until the actual raw boundary.
Array-only callables receive pixels; declared RuntimeArrayData consumers retain
metadata. Their truthful annotation migration changes no scientific function body,
defaults or decorators, as checked across all 19 affected CP modules by AST.

Controls: 646 passed, 5 existing skips, 2 existing warnings. They cover preparation
ordering, rewarm/new compilation, request bindings, custom signatures/defaults,
transport, and 12-plane compiled execution with all signature/hint queries forbidden.
An additional 75 publication/real-payload controls pass, including actual compiled
ColorToGray spatial-mask/channel collapse, MedianFilter intensity scale/mask and
IdentifySecondaryObjects source coordinates/provenance.

The final real isolated registry check prepares 267 catalog entries and 976 targets;
all 267 contracts have snapshots, with zero missing signatures and zero subsequent
owner signature/hint resolutions in contract queries/projections. Its 16.67s
cached-startup duration is diagnostic startup and excluded from pipeline clocks.
The earlier fresh-cache 91.01s startup check remains separately preserved.

Evidence is retained under /home/ts/code/projects/openhcs-benchmark-runs:
issue419-shared-signature-closure-final-receipt-20261002.json,
issue419-actual-shared-signature-closure-readiness-20261002.json and
issue419-truthful-annotation-actual-source-consumers-20261002.json. Earlier failed
intermediates are retained. Current all-case scientific parity and ordinary
performance are separate pending gates; earlier 90c30 timings do not qualify this
new source or updated shared dependencies.
