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

Working production checkpoint. Related source checks and a fresh installed MCP
failed-preparation/valid-registration path remain pending. No original process or
scientific source was adopted. The existing released UI checkout was reused;
foreign gitlinks and historical validation/HDD custody were preserved.
