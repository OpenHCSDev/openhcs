Task-only trial resources and dated software identities
======================================================================

Independent resource audit dated 6 October 2026. The catalogue binds manuscript
and supplementary source snapshot ``dafd55bc6bf351153c0062a13275a4fbf62e2235``.
It contains 68 original author-invocation/operational-phase rows plus the three
earlier prospective assay records. Rows are not pooled experiments: selected
examples, independent repeats, interrupted phases and assisted continuations
remain distinct. No scientific pipeline, reference scorer or paid model run
was executed for this audit. No active author guidance or installed package
was changed.

The exact currently plotted bright-object trial is **H001_FRESH586_96**:
59 of 64 notebook objects matched and first/final F1 0.929/0.944. The plotted
volume trial is **H002_FRESH15_89**, with reported mean matched error about
4.80 voxels. Their resource rows are not substituted by later authors.
Figure numbers can change during manuscript integration; the trial identities
and existing evaluation receipts are the binding facts.

Clock boundaries
----------------

``native_task_started_utc`` is the original native author journal's
``task_started`` event. It starts the turn/setup, not demonstrated brief
delivery. ``brief_instruction_utc`` is the first non-environment user message
in that invocation directing the author to read the already released
``TASK.rst``. All elapsed columns below use this **recorded instruction
delivery** timestamp. It is not the task-file creation time, recorder launch,
MCP startup, or the later time at which reading the full task file completed.
For example, H001 fresh586 setup started at05:09:07.423 UTC, while its
instruction was recorded at05:09:08.701 UTC. H002 fresh15 started setup
at17:15:47.578 UTC and received the instruction at17:15:49.141 UTC.

``first_terminal_utc`` is the earliest retained non-compilation scientific
execution end timestamp from the original MCP/native status receipts;
``first_elapsed_s`` is time from instruction delivery to that endpoint.
This is the **initial scientific prediction-attempt terminal boundary**, before
its subsequent visual QA. It does not choose an evaluator-best intermediate
or require an error-free first command. A failed terminal status stays failed.
In H002 fresh15, the original report and technical-repair receipt establish
that outputs were materialized before viewer settlement failed; the unchanged
scientific method continued in a distinct technical revision. Likewise the
BBBC039 fresh612 initial attempt wrote native artifacts before a redundant
metadata step failed. The elapsed resource boundary includes that finalization
failure. It is not a claim of successful FIRST QA. For another failed attempt,
the number alone does not establish that a completed prediction existed:
consult the original report and retained failure before using it as the
paper's FIRST completed-prediction comparison.

``task_end_utc`` is the original author's ``task_complete`` event.
``final_elapsed_s`` runs from instruction delivery to that event, including
self-directed repairs, QA, reporting and owned cleanup. It is **whole task
walltime**, not time to the last scientific pipeline, pure model compute,
or the time of pipeline freezing. Coordinator evaluation and post-writer
sealing are excluded. Execution duration is a different clock and is never
substituted. Seconds are rounded to0.001; original UTC endpoints remain in
the CSV. These clocks report elapsed time, not a reliability or quality ranking.

BBBC013_FRESH15_96 has separate original and recovered invocation rows keyed by
their actual thread identities. The original phase has no retained
``task_complete`` boundary, so its final elapsed task time is
``not_recorded``; the recovered phase is not another independent author.
No time is inferred from process disappearance or file modification times.
Assisted continuations have phase walltimes, not a reconstructed cumulative
fresh-run duration. No fixed75-minute ceiling is inferred from a run name.

Resource and cost accounting
----------------------------

Token counts are original CLI ``turn.completed.usage`` counters, corroborated
where available by the native ``token_count.info.total_token_usage`` event.
Cached input is a subset of input; reasoning output is a subset of output.
Neither is added a second time. Tokens can count repeated context presentation,
so they are not the size of the unique transcript. For interrupted/recovered
phases lacking a CLI completion counter, the CSV identifies the native
cumulative counter explicitly.

Retained-context P001 and other development counters can include ancestors.
They remain marked ``retained_context_cumulative_not_incremental``; they
must not be summed across phases, compared with fresh-invocation usage as
though incremental, or priced as isolated repair work. In particular,
P001_ALLCHANNEL_RETAINED_DEV25_88 reports85,635,218 input and268,096 output
tokens at completion, but this is a retained-context total, not demonstrated
incremental usage for its approximately54.62-minute phase.

Configured provider ``openai`` and literal model alias ``gpt-6.1-sol``
come from original ``session_meta`` and ``turn_context``, not today's
configuration. They do not prove an API-billed route, immutable backend model
revision, or model release date. The earlier prospective study's
``gpt-5.6-sol`` is identified as paper-reported; its bound archive contains
MCP transcripts but no located author/provider usage receipt.

Every provider-billed USD field is ``not_recorded``. Every listed-API-price
estimate is ``not_calculated``. Neither means zero cost or free operation.
No current price is applied retrospectively. The missing dependencies for an
actual cost table are original billing/credit receipts with a trial or
invocation allocation, a demonstrated billing route, and any applicable
historical rates; subscription allocation cannot be invented from tokens.
No such billing owner receipt was supplied by the bound trial records.

Selected examples and explicit repeats
--------------------------------------

These compact rows are available for parent manuscript integration.
The initial endpoint's status is included so technical failures are not hidden.
The complete CSV retains other reported repeats, unsuccessful histories,
assisted phases, original roots, thread-journal paths and SHA256 identities.

.. csv-table:: Instruction-to-initial-terminal and whole-task walltimes
   :header: "Original trial", "Initial min", "Task min", "Input tokens", "Cached input", "Output tokens", "Initial terminal status"

   H001_FRESH586_96,13.54,44.82,16954462,16489344,45046,complete
   H002_FRESH15_89,20.20,43.33,20644009,20160128,47070,failed
   H003_FRESH26_89,12.07,54.89,25359561,24510464,76112,complete
   R0010_FRESH09_96,25.98,77.75,18927374,18346880,67642,complete
   R0010_FRESH26_94,10.84,41.25,23443911,22882944,61636,complete
   H004_FRESH20_95,10.14,30.95,15641682,15162880,46709,complete
   BBBC039_FRESH612_96,21.28,69.14,20509253,19833344,55281,failed
   BBBC039_FRESH10_COVERAGE_96,30.13,77.86,20307910,19415552,57826,complete
   BBBC039_FRESH13_88,23.66,174.62,57445074,55888000,180266,failed
   BBBC007_FRESH26_96,18.83,90.76,34477288,33369728,105264,complete
   BBBC013_FRESH23_96,18.10,213.10,77735553,75847680,295681,complete
   P001_FRESH13_96,29.16,72.55,18615457,17656192,56533,complete
   P001_ALLCHANNEL_RETAINED_DEV25_88,8.66,54.62,85635218,82549504,268096,complete

The independent nine-field P001 row is not the assisted mosaic row.
First/final biological scores remain in their existing evaluation owners;
none was recomputed or returned to an author. H001_FRESH25_FOURTH_95 and
H001_FRESH25_ROTATION_94 remain separate repeats. The earlier supplement
label ``BBBC039_FRESH594_96`` resolves through its original evaluation
receipt to actual writer ``BBBC039_FRESH594_88``; the CSV records that
actual identity, not a fabricated second run. Development source-filter
widening, operational input repair, and explicitly assisted repair are not
converted into blind autonomy by this resource catalogue.

Dated models and software table
-------------------------------

Dates are **observed trial instruction dates in UTC**, not software/model
release or installation dates. The original recorded health response owns
OpenHCS version; ``session_meta`` owns CLI/provider and ``turn_context``
owns model alias. Delivery is the frozen target used by that original trial.
Full source pins, skill entrypoint hashes and original mount paths are in the
CSV. A skill date is its corresponding dated delivery observation, not the
host-global skill directory's mtime. No later merged guide is credited to an
older trial.

.. csv-table:: Recorded dated identities
   :header: "Observed UTC", "Model alias", "Provider label", "CLI", "OpenHCS", "Delivery", "Source pin prefix"

   2026-09-16,gpt-5.6-sol (paper-reported),not_recorded,not_recorded,0.8.5,earlier prospective MCP archives,not_recorded
   2026-10-04,gpt-6.1-sol,openai,0.160.0,0.8.7,engineering494/target10,not_recorded
   2026-10-04,gpt-6.1-sol,openai,0.160.0,0.8.7,openhcs-issue-batch-20260929/engineering585,f4568ded6b6c
   2026-10-05,gpt-6.1-sol,openai,0.160.0,0.8.7,engineering-pre-first-routing-20261004/receiving19,87908bac61cd
   2026-10-06,gpt-6.1-sol,openai,0.160.0,0.8.7,engineering-pre-first-routing-20261004/receiving22,d068b3f23475
   2026-10-06,gpt-6.1-sol,openai,0.160.0,0.8.7,engineering-pre-first-routing-20261004/receiving25,ed2f37cc547e
   2026-10-05,gpt-6.1-sol,openai,0.160.0,0.8.7,engineering-pre-first-routing-20261004/receiving15,543bf34669f2
   2026-10-06,gpt-6.1-sol,openai,0.160.0,0.8.7,engineering-pre-first-routing-20261004/receiving23,76240752fe70
   2026-10-04,gpt-6.1-sol,openai,0.160.0,0.8.7,engineering-pre-first-routing-20261004/receiving04,769c1eb81393
   2026-10-05,gpt-6.1-sol,openai,0.160.0,0.8.7,engineering-pre-first-routing-20261004/receiving10,42a787f3911a
   2026-10-05,gpt-6.1-sol,openai,0.160.0,0.8.7,engineering-pre-first-routing-20261004/receiving16,4c39b83a7e25
   2026-10-06,gpt-6.1-sol,openai,0.160.0,0.8.7,engineering-pre-first-routing-20261004/receiving26,77c3a34f7787
   2026-10-05,gpt-6.1-sol,openai,0.160.0,0.8.7,engineering-pre-first-routing-20261004/receiving20,396383e443d9
   2026-10-05,gpt-6.1-sol,openai,0.160.0,0.8.7,engineering-pre-first-routing-20261004/receiving09,6dcb203864e3
   2026-10-05,gpt-6.1-sol,openai,0.160.0,0.8.7,engineering-pre-first-routing-20261004/receiving13,2f4c68ff0587
   2026-10-04,gpt-6.1-sol,openai,0.160.0,0.8.7,engineering-mcp-queued-cancellation-20261004/receiving03,not_recorded
   2026-10-04,gpt-6.1-sol,openai,0.160.0,0.8.7,engineering-pre-first-routing-20261004/receiving08,6e1e69e480e8
   2026-10-03,gpt-6.1-sol,openai,0.160.0,0.8.7,official30-package-implementation-20261003/scratch,not_recorded
   2026-10-04,gpt-6.1-sol,openai,0.160.0,0.8.7,engineering-pre-first-routing-20261004/receiving03,5ab324beb450
   2026-10-04,gpt-6.1-sol,openai,0.160.0,0.8.7,openhcs-issue-batch-20260929/engineering594,7fb3c09b090a
   2026-10-03,gpt-6.1-sol,openai,0.160.0,0.8.7,engineering494/target08,not_recorded
   2026-10-04,gpt-6.1-sol,openai,0.160.0,0.8.7,engineering-main2b-retina-20261004/receiving03,ebd622707bea

``skill_hash_scope=retained_original_mount_file`` means the retained path
named by the original launch command was hashed. For the older engineering585
and receiving08 targets, the old mounted entrypoint is no longer readable;
the preserved, originally qualified managed delivery copy supplies the hash
and is explicitly labelled ``qualified_managed_delivery_copy``. This is
not a new claim that the old mounted file was rehashed. Missing identities
remain ``not_recorded``. CLI and model release dates and immutable
backend model revisions were not recorded and are not inferred.

Original owners and readback
----------------------------

`Complete resource CSV <trial_resources.csv>`_ contains one scalar summary
per original invocation or explicitly separate continuation. This file is a
paper projection, not a new ledger, recorder, payload store or source of
scientific state. Native provider journals and original MCP stdout remain
the evidence owners. All original files, frozen manifests and UNKNOWN
operations remain unchanged.

MCP response readback used existing
``openhcs.mcp.recorded_evidence.RecordedMcpJournal.index`` and
``RecordedMcpResponseReference.result``, introduced by merged1030, through
the existing paired interpreter and immutable receiving28 dependencies.
No new parser, package install, environment, worktree, runtime or GUI was
created. Provider fields were read directly from original CLI/native JSON
event records. Hashes in the CSV identify the bytes read for this audit;
they do not retroactively replace original snapshot/prefix seals or claim
whole-payload verification beyond the existing completion/evaluation receipts.

The original plotted H001 root is::

  /home/ts/wt/openhcs-issue-batch-20260929/next-h001-fresh96-guide586-20261004/H001_FRESH586_96/author-workspace/output

Its original native thread is ``01a10550-da58-72d1-9761-c0a21ef7f36f``;
FIRST execution is ``20cc1033-0276-4252-ab16-716d04043b30``.
H002 fresh15's original root is::

  /home/ts/wt/openhcs-issue-batch-20260929/next-h002-fresh15-89-after-retina-20261005/H002_FRESH15_89/author-workspace/output

Its native thread is ``01a10d10-7fb8-72b0-8571-8ce0dda01429``;
FIRST terminal execution is ``79131a7b-baff-4d90-b1d1-3a3ba047110c``.
The existing H001/H002 evaluation receipts bind these plotted runs separately
from their later repeats. No reference arrays were opened for this audit.

The older three prospective rows retain their existing assay archive paths.
Their MCP transcript spans do not establish full author-task walltime or
provider usage: absent author-delivery/completion journals and billing records
are stated as missing, rather than pricing MCP execution time or reconstructing
model cost. This limitation does not invalidate their existing scientific
evaluation receipts.

Checkpoint acceptance: all 71 phase identifiers are unique; every recorded
elapsed value recomputes from its original UTC endpoints within 0.001 seconds.
All 68 modern native-journal SHA256 identities matched retained bytes on
readback. Cached-input/reasoning subsets and explicit missing-cost fields
passed consistency checks. These are resource-accounting checks, not a new
scientific evaluation or a claim that 71 independent experiments were run.
