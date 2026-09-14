# Hosted CI repair evidence (2026-09-14)

## Scope

This dated ledger records the failures and repairs encountered while adding
Official30 value-comparison coverage. It is evidence about particular source
snapshots and hosted jobs, not an authority for installer or benchmark
semantics. Those remain in their owning source and tests.

## Python formatting gate

The full-scope Black gate initially reported 16 existing Python files under
`paper/`. Commit `7a7d21fee` formatted exactly those files with Black 26.5.1.
The before-and-after files had identical Python ASTs. The gate remained
full-scope; no baseline selection or exclusion was added. Hosted code-quality
job
[`104115113553`](https://github.com/OpenHCSDev/openhcs/actions/runs/34885400794/job/104115113553)
subsequently passed.

## Cold Intel GUI discovery

The Intel macOS installed-application smoke test exhausted its 180-second
discovery interval during a cold first launch. Commit `a46e38191` changed only
the declared installed-GUI smoke timing: discovery is allowed 300 seconds and
the enclosing process ceiling is 330 seconds. The required visible-window,
process-lifecycle, screenshot, and MCP assertions were unchanged. Hosted Intel
macOS installer job
[`104100932284`](https://github.com/OpenHCSDev/openhcs/actions/runs/34881128852/job/104100932284)
passed the source contract and full installed application after that change.

## Native busy disk-image contract

Hosted Intel macOS jobs
[`104115113501`](https://github.com/OpenHCSDev/openhcs/actions/runs/34885400794/job/104115113501)
and
[`104126198226`](https://github.com/OpenHCSDev/openhcs/actions/runs/34888719331/job/104126198226)
failed the native HFS+ disk-image test. The test intentionally kept a Python
process's current working directory and an open file descriptor on the mounted
image. The retained diagnostics identified that holder and showed that forced
volume unmount completed while whole-device eject remained resource-busy.

The old test expected cleanup to eject the image while that external holder
was still alive. That expectation was invalid: retrying the owned device cannot
make a deliberately persistent external holder release its references, and
terminating an unrelated process would exceed cleanup ownership. Commits
`66261303f` and `5667b761b` tried bounded eject retries; the second failed after
all five attempts while the holder remained alive. The retry implementation is
therefore superseded by the contract below rather than treated as a successful
lifecycle repair.

An initial correction then assumed the mounted-path holder would always block a
forced native detach. Exact-head job
[`104131281843`](https://github.com/OpenHCSDev/openhcs/actions/runs/34890252544/job/104131281843)
disproved that assumption: the same fixture detached the whole device and the
helper returned success. Across the three receipts, an open mounted file and
working directory can coincide with either a retained resource-busy device or
a successful forced detach. The native test therefore checks state rather than
requiring either operating-system outcome:

1. return status must agree with presence or absence of the exact owned device;
2. if the device remains busy, failure is visible and the device is retained;
3. after the test releases its own holder, any retained device cleans up and is
   proven absent;
4. conversion, verification, remount, and payload-integrity checks proceed;
5. no cleanup code signals or terminates the external holder.

Deterministic unit cases continue to require the visible failure and retained
device when their simulated operating-system state refuses both normal and
forced detach. A separate native raw-device holder proves that holder
diagnostics include root-owned raw handles; it is not treated as an undocumented
guarantee that macOS must refuse a forced eject.

The shell helper retains a single forced whole-device detach following explicit
volume release and returns failure if the exact owned device remains present.
It does not hide resource-busy failure behind a retry loop. On Linux, the full
installer suite passed 103 tests with the one native macOS test skipped. Hosted
native verification of the corrected contract is pending at this ledger's
commit boundary and must not be inferred from the local result.

## Official30 cross-check

The corresponding benchmark evidence is recorded separately in
[`official30_value_completion_20260914.md`](official30_value_completion_20260914.md).
Hosted run
[`34885400794`](https://github.com/OpenHCSDev/openhcs/actions/runs/34885400794)
passed the full 30-workflow historical parity job after the label-aware shrink
correction. This receipt is independent of the five-workflow augmented export
suite and does not change the historical comparison inventory.

## Local validation

The final installer contract was checked with:

```text
timeout 165 .venv/bin/python -m pytest -q -c tests/installer/pytest.ini tests/installer
# 103 passed, 1 skipped in 78.29s
```

The native test is deliberately skipped off macOS; only a terminal hosted
Intel macOS job can close that platform-specific evidence boundary.
