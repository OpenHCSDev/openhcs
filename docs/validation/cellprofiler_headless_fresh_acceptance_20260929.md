# Authorized fresh bootstrap acceptance

Owner: `openhcs-headless-bootstrap-worker` (Singer), issue #138, draft PR #207.
Owner authorization now permits normal fresh dev acceptance, but **only after
Euler explicitly releases the shared heavy-validation slot**. Do not poll or
spin on `/home/ts/wt/openhcs-issue-batch-20260929/validation.lock`.

## Owned output and limits

- Disposable root: `/home/ts/.cache/agent-scratch/openhcs-issue-bootstrap-20260929`.
- Purpose: fresh CP/core 4.2.8.1 oracle, explicit pip cache, build temporary files.
- Maximum aggregate owned disposable allocation: 4 GiB. No whole-cache copy.
- Persistent logs/receipts: this worktree's `docs/validation` directory; retain
  failed-build logs and exact command/source/pin evidence before cleanup.
- Interpreter: existing `/home/ts/code/projects/openhcs/.venv-cellprofiler39/bin/python`
  (3.9.25). JDK: existing `/usr/lib/jvm/java-11-openjdk`. No Python/JDK download.
- Public declared-pin package downloads are allowed; inspect relevant existing
  wheel cache first. The initial pip wheel-cache listing contained no native CP
  wheels (only an unrelated package), so do not copy unrelated cache contents.
- No installed user package/source change, GUI, fleet, paid service or blind data.

## Run once the slot is released

Run the resource guard immediately before building and preserve at least 8 GiB
available RAM. Acquire the shared lock nonblocking once; if unavailable, do not
retry in a loop. The entire build and native acceptance must hold that lock.

Create a new attempt directory under the owned root. Place the oracle, pip cache
and `TMPDIR` there. Run the current worktree's real `create` command with:

```sh
/home/ts/code/projects/openhcs/.venv/bin/python \
  scripts/bootstrap_cellprofiler_headless.py create \
  --python /home/ts/code/projects/openhcs/.venv-cellprofiler39/bin/python \
  --java-home /usr/lib/jvm/java-11-openjdk \
  --venv /home/ts/.cache/agent-scratch/openhcs-issue-bootstrap-20260929/attempt-001/oracle \
  --cache-dir /home/ts/.cache/agent-scratch/openhcs-issue-bootstrap-20260929/attempt-001/pip-cache \
  --receipt "$PWD/docs/validation/cellprofiler_headless_fresh_attempt001_20260929.json"
```

Keep resource supervision on the owned running build, not on Euler's lock or
process. Stop the owned build before exceeding the 4 GiB budget or violating
RAM headroom; retain its failure/output evidence. Build subprocesses are bounded
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

Authorized, not started: waiting for Euler's release notification. No lock check,
build, download, new environment or JVM was initiated to obtain this slot. The
previous source-hashed receipts remain valid only for their recorded sources.
