# PR233 finite source-live handoff

Owner transfer: parent runs the next finite source-live journey, reviews/merges,
installs this same frozen tree and then proves installed entrypoint. Lovelace
has not started attempt03. No handles currently live. Do not edit this source
during the journey or after parent adopts it for installation.

Tree: /home/ts/wt/openhcs-custom-function-admission-20260929
Draft: https://github.com/OpenHCSDev/openhcs/pull/233
Frozen commit: the onboarding follow-up SHA reported in the handoff message.
Normal main240 merge d33128916 / main3032958ac is included. All eight recorded
submodules remain unchanged, PolyStore1209068. Both compiled abi3 artifacts are
present in this source tree; no installation occurred.

Source receipts:

- registration_onboarding_20260929:10passed,2deselected,8.20s,308356KiB.
  Two real-default-context/generated MCP cases reach first_use/pipeline ->
  complete canonical guide -> preparation capability discovery without endpoint
  contact. Skill validator passes. Initial failures and unchanged image-analysis
  context overflow are preserved in scope.md / pytest_initial.txt.
- registration_main240_tests_20260929:16passed,5.53s,293380KiB.
- registration_main240_build_20260929:2.55s,146140KiB,exit0; both source extension
  import paths/hashes captured. Their temporary objects/library copies and bounded
  test scratch (~936KiB combined) were removed; source artifacts and receipts remain.
- registration_attach_only_20260929:57passed,25deselected,7.22s,309668KiB.

All receipt directories are under tests/runtime_diagnostics. Original attempts01/02
remain immutable, with original synthetic scratch retained for same-handle diagnosis.
Attempt02 status was responsive but redundant100s sub-budget ended before actual
READY at110.50s. All its endpoints/MCP/child are terminal; no mutation happened.
No warmup performance improvement or installed acceptance is claimed.

## Next invocation

Recheck /home >=20GiB, availableRAM >=8GiB before launch; only historical swap
warning is waived. Latest own guard was /home19.8GiB, so no native run began.
The driver itself rechecks headroom and acquires validation.lock nonblocking;
do not wrap another competing runtime/lock around it. Use a TTY and preserve
the same handle if it pauses after any unexpected disposition. It never replays.
Replace FROZEN_HEAD with the exact reviewed onboarding SHA, not a moving main.

```sh
cd /home/ts/wt/openhcs-custom-function-admission-20260929
env OPENHCS_CPU_ONLY=true PYTHONDONTWRITEBYTECODE=1 \
  PYTHONPATH=/home/ts/wt/openhcs-custom-function-admission-20260929:/home/ts/wt/openhcs-custom-function-admission-20260929/external/ObjectState/src:/home/ts/wt/openhcs-custom-function-admission-20260929/external/PolyStore/src:/home/ts/wt/openhcs-custom-function-admission-20260929/external/arraybridge/src:/home/ts/wt/openhcs-custom-function-admission-20260929/external/metaclass-registry/src:/home/ts/wt/openhcs-custom-function-admission-20260929/external/pycodify/src:/home/ts/wt/openhcs-custom-function-admission-20260929/external/pyqt-reactive/src:/home/ts/wt/openhcs-custom-function-admission-20260929/external/python-introspect/src:/home/ts/wt/openhcs-custom-function-admission-20260929/external/zmqruntime/src \
  POLYSTORE_IMAGEJ_CACHE_ROOT=/home/ts/.cache/polystore/imagej \
  POLYSTORE_IMAGEJ_ALLOW_DOWNLOAD=false \
  /home/ts/code/projects/openhcs/.venv/bin/python -B \
  tests/diagnostics/check_custom_registration_live.py \
  --released-runtime-slot --expected-source-sha FROZEN_HEAD \
  --receipts tests/runtime_diagnostics/registration_live_20260929_attempt03 \
  --scratch /home/ts/.cache/agent-scratch/openhcs-registration-live-230-20260929-attempt03 \
  --port 15997
```

Ports15997/15998/15999 must be absent before launch (driver checks). Three headless
owned/foreign/unsupported synthetic fixture servers only, threads1, scratch<80MiB,
no GUI/JVM/download/install/science/shared7777. Total journey240s, each observation10s,
no redundant100s preparation cap. Existing typed start/status/stale-cancel observe
one future; exact audit requires zero source-bearing registration before READY,
exactly two total (initial plus controlled delayed reply), unchanged escaping-path
sentinels, then ordinary register/discover/compile/execute8x8 plus-three and same-
handle uncertainty reconciliation. Added onboarding calls are read-only and precede
first catalogue search. Captures and stage timing persist before disposition.

On unexpected failure, retain original inputs/handles; inspect the same owner,
then use diagnostic `close-owned` only for supported identity-verified cleanup.
Do not restart/replay or inflate timeouts. On terminal, verify all recorded PIDs
absent and lock released before edits. Acceptance remains source-live, not installed.

Later installed proof uses this same driver with --installed-entrypoint, PYTHONPATH
unset and cwd outside this source; ordinary McpDevServerSpec validates actual installed
OpenHCS/PolyStore paths. Parent owns that journey after reviewed merge/install.
Multiprocessing/cold hydration profiling is separate follow-up scope, not this gate.
