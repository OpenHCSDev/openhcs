Headless bootstrap: observed resources, no arbitrary admission quota
=================================================================

PR207 original headbd164a94f0a42b90b45d7f8e43d09314d5fcaccf was inspected
against main674ddefe5b3912720c2e3bdd73ecf5398ebbdc44. Current public owner
comments still named Singer, with no competing current open source PR. Singer
posted the exact finding/claim in comment6002752400 and reused the completed
UI-workflow checkout, merging current main normally. No foreign gitlink was
edited and no installed prefix, receiving18/19 or scientific source was changed.
The checkout's prior cold-relocation release was explicitly suspended in the
parent custody handoff while this source is active.

Determining owner/consumer closure
---------------------------------

Original require_creation_headroom562–574 imposed fixed4GiB disk and8GiB RAM.
Its single production caller was CreateCommand804; two mocked create tests
bypassed it and the low-capacity test asserted the arbitrary refusal. The
how-to and pending acceptance plan repeated those quotas and an old Euler hold.
Those live decisions/references are removed, not retained under an alias.
Original historical receipts are not rewritten as new passes.

The target-owning VenvCapability now exposes its resource-observation hook to
both PlanCommand and CreateCommand. CreationResourceObservation owns the two
measured byte quantities; the existing TypedJsonRecord owns their JSON codec.
Create captures once, logs before commands and preserves that same observation
with failed construction or successful verification. No substitute threshold,
admission framework, new dispatcher, cache copy, store or codec was introduced.
Strict new-target/receipt, Python3.9.25, JDK11, dependency/version and native
lifecycle guards remain. Existing cooperative parser/MRO and command/stage
diamond controls are unchanged and exercised.

Before editing, the existing refactor-audit Package/Overlay parsed the complete
scripts production root:92 modules,0 parse omissions. The determining family
was read directly: resource check, Venv/Oracle/Evidence capabilities, Plan/Create,
subprocess/native receipt owners, constraints, all search-resolved resource
callers and their test/doc consumers. The existing focused source guard reports0
findings both at the original head and after this change. This is scoped AST
evidence, not complete global NRA/R1 proof; unrelated scripts findings were not
waived or turned into work. Applicable catalog concerns: AGENT-7 obsolete
holds, AGENT-8 tooling ownership, BOUND-2 existing typed receipt owner and
TIME-1 deletion of the replaced admission path.

Qualification and remaining exact boundary
-----------------------------------------

The original focused suite passed53 controls in0.42s, including actual create
dispatch under low disk/RAM observations, success/failure evidence, strict
native receipt validation, and independent MI diamonds. It used the existing
paired Python, disabled unrelated pytest plugins and conftests; no application
replacement, OpenHCS cold import or JVM launch was used as a test substitute.
Two existing pytest configuration warnings remain in the original log.

The ordinary script's real plan entrypoint also passed using existing native
CPython3.9.25 and actual JDK11.0.32.1. It returned four declared construction
commands and measured free disk155852849152 / available memory12102885376 bytes.
The proposed target was not created. Guard telemetry before checks reported
12.1GiB available RAM with disk/existing-swap warnings; no invented hard cap was
set or increased. Changed source/docs diff-check passed.

Original controls01 stdout/stderr, owner-before01/after01 JSON, AST coverage and
public-plan01 JSON/stderr are preserved byte-exact in the accompanying tar.gz.
The local validation/headless-bootstrap207 directory retains the originals.

Fresh creation is NOT qualified. Read-only installed metadata confirms the
existing oracle still has setuptools69.5.1 instead of declared80.9.0; the pip
wheel-cache listing contains no complete native/CP closure. Singer remains the
integration owner for obtaining an admitted exact cached artifact closure and
the original receiving-lane handoff before fresh creation. Do not upgrade the
oracle, downgrade pins, copy shared Fiji caches, fetch new dependencies or call
existing-oracle verification a fresh bootstrap proof. Issue138 remains open;
CI is not the blocker. No build/download/new environment/JVM or science was run.
