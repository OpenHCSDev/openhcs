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

Source checkpoint and actual controls
------------------------------------

Draft PR511 was published at 3e1e336089ccf2d3d3e20a849a885193daff1bba before
longer verification. The postchange selected-family AST receipt has 28 production
modules, 5262 sites, 8 dependency modules and zero parse errors. Runtime claims
remain separate from this evidence. ``git diff --check`` passed.

All four bounded collection attempts are retained in the original engineering
receipt root as catalog511-source01..04.log/time; each used CPU1/512MiB/Swap0/60s.
They executed no scientific functions, native servers, sockets or viewers:

1. systemd working directory omitted: pytest rejected relative confcutdir.
2. corrected directory: dependency import preceded source bootstrap; corrected
   the test import ordering through the original source owner.
3. collection then reached missing compiled openhcs.core._tabular_native.
4. reused the accepted505 real extension directly, without copying/building it;
   its C++ source matches this checkout, SHA256 of the ABI3 extension is
   7de8f671e79263518e56219b30085b2c39c9518db63739298c4ffc9265196aae.
   Collection then failed because the protected old external/zmqruntime checkout
   lacks ViewerReuseAdmissionABC required by current-main viewer_protocol.

No assertions ran: this is a precise dependency-collection blocker, not a passing
regression suite. Attempt04 peaked at 179752KiB RSS (unit peak123.3MiB), zero swap,
3.015s. The last run reused an explicit actual compiled dependency for source
controls only; it is not ordinary installed/public/native acceptance. No substitute
registry/factory/backend, native extension stub, path fallback or protocol was
introduced into production. All foreign external trees remain unchanged. They
will not be updated, patched or bypassed to hide this source-import boundary.

The authored controls cover warm full/compact public projection, current-source
revision, add/update/delete/body-only invalidation, refresh coalescing, retained
failure/cancellation, incarnation rejection and original main-thread startup.
Run them using current qualified dependencies after an explicit receiving release;
then perform the separately authorized ordinary installed native public journey.
No build, installation or native launch was performed. Saved diagnosis and all
scientific records remain immutable.
