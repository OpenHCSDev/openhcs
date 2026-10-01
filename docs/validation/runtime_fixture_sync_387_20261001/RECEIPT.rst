Runtime fixture synchronization (#387)
======================================

Unchanged main ``10f7e7075b412ccea8959f2c4e1aa818455149fa`` reproduces four
runtime-value fixture failures (4 failed in 1.88s). Three fixtures assert a
source filename extension without declaring it; the fourth expects rows where
the merged materialization contract returns a typed MeasurementTable.

The repair declares the asserted .tif extension in fixture source metadata,
preserves all resulting filename and plane assertions, and verifies both table
identity and row contents. No production source, filename inference, numerical
tolerance, or benchmark clock changed.

The complete repaired module passes: 181 tests in 17.60s. The original red and
complete green pytest output and JUnit documents are retained beside this
receipt. The test-only worktree used the shared Python3.12 environment and exact
native binaries from main. Extracted-package imports use the existing shared
checkout at the same eight declared dependency revisions. This test-only
qualification does not claim a performance improvement or a native CP ratio.

Validation commands::

    OPENHCS_CPU_ONLY=true python -m pytest -q tests/unit/test_runtime_values.py
    git diff --check

These fixtures were identified during generic runtime plumbing qualification
(#384); the performance changes are separate and remain unqualified.
