Failed custom-source preparation retention (#131)
================================================

Current-main source proof
-------------------------

``CustomFunctionRuntimeRegistry`` owns one preparation Future per exact source
revision. Previously its cached exception retained the factory's traceback and
cause, including ``CustomFunctionManager._prepare_source``'s execution namespace.
Repeated ``Future.result`` calls raised that same exception and extended its
traceback. A bounded standard-library check retained an otherwise unowned payload
and grew traceback depth 1, 4, 7, 10, 13 across four failed reads.

This is a concrete retention mechanism, not proof that the original P001 process
exercised it or an explanation of its 3,734,000 KiB private-resident-plus-swap
observation. Cold BioFormats/JVM-associated growth remains separately accounted.
No scientific request, original uncertain source revision, GC or restart was used.

Owner and consumer change
-------------------------

``CustomFunctionPreparationFuture`` specializes Python's existing Future failure
lifetime. It caches a traceback-free exception copy and original formatted
traceback evidence, never a TracebackException object holding source-local types.
Each result reader receives a fresh exception with the same type, message and
declared values. Successful metadata identity, waiting/cancellation behavior,
source revision keys, retirement and exactly-once execution remain with their
original owners. Failed cache entries are not evicted to trigger re-execution.
``ValidationError`` owns copying its original message/line/snippet values.

Before-edit AST closure used the existing refactor-audit Package/Repository over
custom-functions, library-registry, agent services and unit tests: 687 parsed
modules, zero omissions. The three manager callers are load-all, load-one and
unchanged update. Registry creation, lookup, stale-revision removal, declaration
retirement, reconcile and clear are retained. Endpoint catalog preparation Futures
are released by their request lifetime, not kept in this source-revision cache;
they are not replaced by a second failure store. Python's Future exception/result
implementation was read separately. These are focused source facts, not a global
architecture or memory correctness claim (IDEN-1: failure evidence vs live frames).

Qualification
-------------

Production pin f97cdf41604a4de5b1ef3ad5225dc8bc3941a881. Original offline whole
builder terminal0, 2:13.11 total, 443360 KiB peak RSS, zero swaps. Whole wheel,
installed RECORD/source bytes and ordinary managed skill sync passed through the
existing receiving28 materializer/verifier and the same five dependency wheels.
Both affected installed modules are byte-equal to this source. No environment,
shared install, dependency download or Fiji initialization was added.

Related original test modules, byte-identical copies against the installed target:
77 passed in6.52s (10.84s process, 378424 KiB peak, zero swaps). This includes
concurrent exactly-once failed loads, immediate request payload release WITHOUT
explicit GC, fresh exception identity, stable repeated traceback depth, preserved
type/message/line/snippet and original cause evidence, success identity, timeout,
cancellation, canonical lookup and startup/source retirement lifetimes.

Fresh MCP case07 used the installed diagnostic entrypoint and original public
``openhcs_create_orchestrator_session_from_pipeline_source`` capability. Four
imports returned identical declared ValidationError diagnostics; the new failed
source's own counter proves exactly ONE execution. A separate valid custom source
created session-5 successfully. This was source-session creation, not compile,
scientific execution, a native catalog or viewer. Original MCP3852349 exited0 and
was absent after normal session closure. Original client34735 terminal0,
12.74s/362776 KiB peak, zero swaps. Natural private-dirty-plus-swap samples were
213156 then215308 KiB with host full PSIavg10=0; this short observation is NOT a
long-workload slope or attribution of the original P0013.56GiB.

Exact retained artifacts (HDD, not HOME reclaim):
``/run/media/ts/hdd/openhcs-cold-custody-20261003/engineering-mcp-retention-131-failure04``
contains BYTE-QUALIFICATION.json, SOURCE-PIN/ORIGIN, build01.log/time,
installed02.log/time, LIVE07.json, live07.log/time/stderr, the whole wheel/target,
and immutable runtime07 source fixtures. verify_failure_mcp.py and both selected
fixtures are published beside this receipt for reproduction in a NEW named case.

Original negatives remain: source01 collection used foreign old PolyStore and
failed import before assertions; installed01 had no collected files from a
relative-copy path mistake; live04 failed before source dispatch on an incorrect
driver DTO method; live05 schema rejected an internal connection field; live06
correctly rejected an os import in the synthetic fixture BEFORE execution. No
product guard was weakened. Their original logs, sources and runtime roots remain.

No original process or scientific source was adopted. The released UI checkout
was reused; all eight foreign gitlinks and historical validation/HDD custody were
preserved. #131 remains open for original large-process causal attribution.
The terminal generated source/build subtree (31 MiB) and separate build scratch
are released to Dalton only; source/target/wheel/fixtures/journals/proofs remain
protected. Their relocation would free HDD bytes, not HOME space.
