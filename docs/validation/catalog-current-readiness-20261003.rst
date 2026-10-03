Current native function-catalog readiness
========================================

Owner and reproducer
--------------------

FunctionCatalogService owns the existing metadata-derived public projections;
FunctionCatalogPreparation owns their worker, future, cancellation and progress.
The native READ/SEARCH/DETAIL/REFERENCE template already calls this owner.

The retained H001_REPEAT02 journey demonstrated successful custom registration,
an old READY preparation receipt, and subsequent catalog READ timeout at 4975ms.
An intervening describe succeeded; the preceding search is UNKNOWN, not replayed.
No inner per-callable cost was measured. This is a stale readiness correction,
not a claim that one particular reflection operation has been timed or optimized.

The old successful future was reused forever, while metadata invalidation could
make the next public request rebuild a complete catalog projection in REP. Only
the compact view was prepared before serving; default full-view search could
also cause that work synchronously.

Change
------

* Derive current readiness from the existing projection keys and metadata,
  RegistryService.cached_metadata_snapshot, and the original persisted-source
  revision owners. Do not maintain another generation, catalog or revision cache.
* Prepare both existing public views before advertising READY. Refresh only
  these projections after invalidation, using the original preparation worker;
  do not repeat native kernel startup for an ordinary source change.
* Coalesce pending work; preserve failed/cancelled futures without automatic
  retry. A completed historical future is not current READY after invalidation.
* Apply the existing OperationCancellation to per-callable projection work.
* Leave registration admission, receipt and original invalidation untouched.
  The next public catalog request uses the same existing preparation gate.

Production scope is only agent/services/function_catalog_service.py and
runtime/function_catalog_preparation.py. RegistryService, CallableProjection,
custom-source decoding, compiler, native/MCP protocol and deadlines are excluded.
Root394 was notified before production edits in comments 5965485052/5965541595;
its current 4eaacf17 head does not change these files.

Source and custody
------------------

Parent explicitly released the former programme source claim on the existing
/home/ts/wt/openhcs-input-preparation-20260929 checkout, originally e0dd14ed.
The exact full path matches Dalton's direct ownership response. Parent reports
privileged whole-borrower count 0 and access omissions 0. No source reuse of the
borrowed Singer505 or live436 checkouts was made. The branch was switched
nonrecursively from current main87d9a99; foreign submodule directories and .git
files were not updated/reset/cleaned. Their changed status against current-main
gitlinks is retained and excluded from this change. No environment was created.

Full current NRA/refactor-audit skills, required pattern catalog and applicable
antipatterns were read. The existing selected-family AST receipt covers 28
production modules and 8 installed dependency modules, 5235 source sites, with
zero parse errors. Dynamic behavior is not proven by that receipt. The standing
OPENHCS-HISTORY.md path is absent at main87d9a99 and the canonical checkout; no
replacement reminder/history store was invented.

Acceptance and remaining boundary
---------------------------------

After the coherent source change, bounded controls must cover:

* cold preparation and ordinary startup; warm repeated compact and full views;
* one-worker coalescing after add, same-id update and delete, without kernel rewarm;
* body-only persisted-source changes despite unchanged catalog membership ids;
* historical READY rejection and honest pending progress before refresh completes;
* projection failure, cancellation, retained terminal futures and incarnation mismatch;
* original read/search/detail/reference strategy consumers and admission behavior.

Source controls do not establish installed/native acceptance. A later explicitly
released engineering slot must exercise the ordinary installed public registration,
search, describe and reference journey with unchanged budgets, plus responsiveness
during preparation. No currently live scientist, native, UI or UNKNOWN attempt
will be contacted/replayed. Inner reflection cost remains unmeasured. A registry
inventory lock held by a separate concurrent registry worker is an excluded Root
seam if encountered; it is not silently fixed with another lock or timeout here.

Initial source checkpoint: verification pending; no build, installation or native
launch performed. Saved diagnosis and all scientific records remain immutable.
