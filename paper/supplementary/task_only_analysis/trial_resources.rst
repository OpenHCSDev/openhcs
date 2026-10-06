Task-only trial resources and dated software identities
======================================================

Resource audit dated 6 October 2026. This independent supplementary record
uses original retained author/provider and MCP execution receipts. It does not
execute scientific pipelines, open evaluation references, or return scores to
authors. The catalogue follows manuscript snapshot ``dafd55bc6``; selected
examples, independent repeats and assisted continuations are separate rows.

Clock and accounting boundaries
-------------------------------

``task_start_utc`` is the original native author journal's ``task_started``
event timestamp. ``first_terminal_utc`` is the native execution end time of the
author-designated FIRST scientific attempt, whether successful or failed after
durable scientific output. It is not the first successful compile or an
evaluator-selected best attempt. ``first_elapsed_s`` subtracts task start from
that timestamp. It includes preparation and authoring before FIRST, not its
subsequent visual review. ``task_end_utc`` is the original author's
``task_complete`` event; ``final_elapsed_s`` includes self-directed repairs,
QA, reporting and owned cleanup until that event. Post-writer sealing and
coordinator evaluation are excluded. Pipeline execution duration is a different
clock and is not substituted for either walltime.

Interrupted/reconnected and retained-context development phases are reported
separately where their original invocation boundaries can be established.
An interval spanning interruption includes that gap and must be identified as
such; it is not active model compute time. Missing boundaries are explicit,
never inferred from file modification time or process disappearance.

Token counts are original CLI ``turn.completed.usage`` counters, not tokenized
transcripts. Cached input is a subset of input and must not be added again;
reasoning output is a subset of output. For resumed contexts, inherited or
cumulative usage remains a broader scope unless invocation-only accounting is
demonstrated. Provider ``openai`` is the configured provider identity, not proof
of a billed API route. Model aliases are recorded literally; no dated model
release or immutable backend revision is inferred from them.

No USD amount is inferred from token counts. Provider-billed amounts and listed
API-price estimates are different facts. ``not_recorded`` means the inspected
receipt has no such fact; it does not mean free or zero cost. This audit starts
no paid model run and uses no current price to retrospectively value a trial.

Initial verified checkpoint
---------------------------

H001_FRESH25_FOURTH_95 ran from 03:33:22.056 to 03:58:35.141 UTC on
6 October: 1513.085 seconds. FIRST execution
``5e535029-2ca0-459e-a514-e952f1b9c5e4`` ended at 03:43:36.179086 UTC,
614.123086 seconds after task start. Its approximately 26-second execution is
not the task-to-FIRST walltime. The author selected its final repair independently.
Original CLI usage reports 12,465,437 input tokens, including 12,031,872 cached,
and 36,545 output tokens, including 7,636 reasoning tokens. No billing amount
or price schedule appears in that completion receipt.

Original receipt root::

  /home/ts/wt/openhcs-issue-batch-20260929/next-h001-fresh25-fourth95-20261006/H001_FRESH25_FOURTH_95/author-workspace/output

The root's native journal is
``native-sessions/2026/10/05/rollout-2026-10-05T23-33-22-01a10f45-e5cc-7253-b8c0-600f0dadf1ba.jsonl``.
``trials/attempt01-receipts.json`` retains the FIRST terminal execution;
``runtime/author-events.typescript`` owns the original CLI usage receipt.
``terminal-custody.json`` retains inner-client closure separately from author
completion. The complete catalogue and dated version matrix are being filled
from the same original owners; this checkpoint is not an aggregate cost claim.

.. csv-table:: Verified trial resource rows
   :file: trial_resources.csv
   :header-rows: 1

Dated models and software
------------------------

.. list-table:: Original recorded identities, not current host defaults
   :header-rows: 1

   * - Trial date (UTC)
     - Scope
     - Model / configured provider
     - CLI
     - OpenHCS / skill delivery
   * - 2026-10-06
     - H001_FRESH25_FOURTH_95
     - gpt-6.1-sol / openai
     - 0.160.0
     - 0.8.7; receiving25 frozen target and 13-file skill delivery

The CLI and provider values come from ``session_meta``; the model comes from
``turn_context``. OpenHCS 0.8.7 is the original recorded health response, not a
version read from a subsequently changed installation. Skill dates refer to
the corresponding bundle's qualification record, not host-global file mtimes.

