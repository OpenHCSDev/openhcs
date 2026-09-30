R0: admit an empty R1 head report scope before parsing
====================================================

Owner: parent OpenHCS integration. Issue 274. Audited main:
642821c3c9350a5b28ec1cdc51dcbbad3f8faafb. This is an R0 guard-performance
checkpoint, not a global architectural audit or completion of the archive.

Failure and ownership
---------------------

The original R1 entrypoint compares only changed Python report paths while
retaining full production and recorded dependency context. Comparing main with
L0 PR273 head d9f17dcdc62224a019f7f31626bcf2f4ea3b7233 deletes its only changed
Python file, ``openhcs/formats/pattern/pattern_resolver.py``. The base scan still
parsed full context and failed with ``ScanDeadlineExceeded`` during
``parse_python_module`` at 55 seconds. That run produced no assessment. Its
failure remains valid evidence, not a passing or zero-debt result.

``SourceRevision`` already owns Git membership and recursive committed-source
materialization. It now resolves exact, literal changed paths in the head tree
before materialization. The repository admission check is shared with the
original materializer, so an uninitialized child cannot borrow its parent's
repository. If no changed Python path survives, no head report target can
increase under the existing changed-file policy, regardless of baseline counts.

``R1Assessment`` owns the common revision/change identity and result contract.
``R1Comparison`` retains measured before/after deltas. ``R1EmptyReportScope``
owns the unmeasured empty-scope result and its explicit reason; it has no
before/after count fields. The existing NRA declaration/MRO-derived JSON
projection and the unchanged CLI exit consumer handle both nominal results.
No enum/type/string switch, parallel codec, detector roster or cache is added.

Catalog witnesses are IDEN-7 (the original check wider than its report question),
IMPL-9 (do not encode measured and unmeasured states in one optional bag), and
BOUND-2 (reuse Git and NRA's existing source/projection owners). The only case
decision is at source-scope admission. Leaf behavior stays with its assessment.

Boundaries and new cases
------------------------

The original ``--no-renames`` diff remains unchanged. A move has a surviving
destination, so it follows the original full-context scanner and can report
new-file growth. Literal pathspec admission also preserves filenames containing
brackets, wildcards and tabs. Added or modified Python, parsing failures,
recorded dependency failures, deadlines and per-file growth keep their original
behavior. No budget increase, context reduction or detector omission is made.
No public application format, package, runtime, GUI, saved analysis or image data
is changed. Previous evidence artifacts remain unchanged.

New-case test: adding a moved destination requires no consumer changes; the
same source owner admits it to the original scanner. A new assessment case would
declare its own data and ``increased`` behavior, rather than add CLI branches or
parallel field lists. There is no compatibility reader for the old empty-scope
representation; the internal CLI result now reports its actual evidence scope.

Validation
----------

On 2026-09-30 the complete existing workflow/policy test module plus new cases
passes: 26 tests in 26.05 seconds, zero skips. This includes actual CLI JSON and
exit status, cross-module schema/descent, context invalidation, per-file growth,
malformed source, zero-budget failure for surviving source, missing dependencies,
literal deletion/move identity, empty-scope repository rejection and actual
workflow shell admission. XML is retained in the parent ledger as
``r1-empty-scope-tests-20260930.xml``. No application conftest, JVM, native server,
MCP process, viewer, download, provider or installed-package change is used.

The actual deletion-only CLI comparison against the exact PR273 commit returns
exit 0 in 1.50 seconds at 63004 KiB peak RSS, with a zero-second scan budget:
``reason=no_surviving_changed_python``, the deleted source in ``changed``, and
``increased=[]``. It creates no scratch directory and emits no before/after
counts. This is admission of an empty report scope, not a completed NRA scan.
The source-only change to this guard has not itself received a full production
NRA scan. The resource gate is critical at 16.6 GiB swap, so no such heavy scan
or new native acceptance is started to manufacture stronger claims.
