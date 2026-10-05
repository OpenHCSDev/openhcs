# Authorized fresh bootstrap acceptance

Owner: `openhcs-headless-bootstrap-worker` (Singer), issue #138, draft PR #207.
Singer resumes current integration. The former Euler slot, fixed8GiB RAM veto
and4GiB scratch quota are historical policy, not current admission. Use the
actual receiving-lane owner's handoff for heavy work, without polling an old
lock or waiting on a historical acknowledgement.

## Owned output and limits

- Disposable root: `/home/ts/.cache/agent-scratch/openhcs-issue-bootstrap-20260929`.
- Purpose: fresh CP/core 4.2.8.1 oracle, explicit pip cache, build temporary files.
- Observe actual disk/RAM/pressure and concurrent work; no invented quota.
  Reuse admitted caches without copying them or changing shared Fiji data.
- Persistent logs/receipts: this worktree's `docs/validation` directory; retain
  failed-build logs and exact command/source/pin evidence before cleanup.
- Interpreter: existing `/home/ts/code/projects/openhcs/.venv-cellprofiler39/bin/python`
  (3.9.25). JDK: existing `/usr/lib/jvm/java-11-openjdk`. No Python/JDK download.
- Current authorization permits ordinary missing pinned dependency acquisition
  through the existing isolated bootstrap and shareable pip-cache owner. Do not
  upgrade the old oracle, downgrade pins or redownload Fiji. An existing
  installation is not fresh construction evidence.
- No installed user package/source change, GUI, fleet, paid service or blind data.

## Run once the slot is released

Run the existing resource guard and interpret actual pressure, available RAM,
disk and concurrency before building. The target-owning VenvCapability shares
resource observation between plan/create; its existing typed JSON owner records
available memory and free disk bytes without a fixed admission threshold.
Create logs those facts before commands and retains them with success/failure
evidence. This observation does not waive genuine resource exhaustion.

Create a new attempt directory under the owned root. Place the oracle and
`TMPDIR` there; reuse the existing shared pip cache. The accepted real command used:

```sh
/home/ts/code/projects/openhcs/.venv-cellprofiler39/bin/python \
  scripts/bootstrap_cellprofiler_headless.py create \
  --python /home/ts/code/projects/openhcs/.venv-cellprofiler39/bin/python \
  --java-home /usr/lib/jvm/java-11-openjdk \
  --venv /home/ts/.cache/agent-scratch/openhcs-issue-bootstrap-20260929/attempt-20261005-01/oracle \
  --cache-dir /home/ts/.cache/pip \
  --receipt /home/ts/.cache/agent-scratch/openhcs-issue-bootstrap-20260929/attempt-20261005-01/receipt.json
```

Keep resource supervision on the owned running build, not on Euler's lock or
process. Adjust concurrency if actual capacity or pressure warrants it and
retain failure/output evidence. Build subprocesses are bounded
to 900 seconds per stage; native verification is bounded to 120 seconds.
Never restart an observation timeout to conceal uncertain state.

Require a strict `verified` receipt, all declared versions (including setuptools
80.9.0), only the deliberate wx omission, native imports inside the new oracle,
and actual Java startup → Pipeline construction → shutdown. No diagnostic drift
flag is permitted on create. Copy/preserve logs and receipt evidence in durable
storage, then remove only the validated owned disposable attempt/environment.

## Current state

The lightweight install-isolation checkpoint passed 51 provider-free tests in
0.34 s and the focused real-source ownership guard reported zero findings.
An actual read-only pip24.3.1 configuration load, with injected target/prefix/user
settings, confirmed isolated mode plus disabled config files loaded no redirects.
Plan/Create share one declared cache capability; the stage owner builds the
isolated pip command. No install was needed for this check.

Fresh create now passed once on2026-10-05: all62 exact pins, no dependency errors
or drift, imports inside the new target, Java start/Pipeline construction/stop,
terminal0. See cellprofiler-headless-create01-accepted-20261005.rst and its raw
archive for the installed receipt and resource disposition. Earlier source-only
and original failed/drift evidence retains its exact historical scope. This is
headless bootstrap acceptance, not scientific/GUI benchmark qualification.
