Controlled retained-VALUES repeat for issue #433
================================================

All 16 public measured jobs and 32 strict native-output comparisons passed on
one READY server incarnation, without restarts, forced garbage collection,
process-cache clears, changed collection thresholds or observation exclusions.
This is a finite memory/scientific acceptance gate, not a latency experiment.

Source and entry point
----------------------

The measured source is ``a6c0e1e030ae6b9859c7447541a7f1f89531e1cd``. The
source was frozen on HOME; installed editable dependencies, native binaries,
original input files, controller and native goldens were hashed before and after.
Newer ``origin/main`` (``eea1f25ca86f5ff9bad2d836b8cdeab55be6a8be``) was
recorded before the freeze; this sequence deliberately tests the specified source,
not subsequent compiler/dependency changes.

The controller calls existing ``execute_measured_openhcs_pipeline_on_client``
with original ``prepare_cellprofiler_input_workspace`` declarations and source
universes: 180 references for 3D, two for Speckles and ten for Beginner. All jobs
use one well/one inline thread, CPU5 and existing native thread limits. Mandatory
function-library/kernel READY warmup precedes jobs. The export scope is VALUES,
as in the original OOM; real record counts are 41/26/44 respectively.

The finite sequence is ``[3D, Speckles, Beginner, 3D]`` repeated four times.
The endpoint PID is ``3971124``, create time ``1791086892.75``,
and port 7777 for every measured receipt and typed handshake. All 16 consumed
ordinary compile artifacts are unavailable through actual public compiled-artifact
inspection. Existing terminal statuses and output receipts remain complete.

The native goldens are both fresh measured output sets from qualified V12.
Existing strict scientific/relationship/image/file-inventory owners compare each
job to both sets: 32 comparisons, all PASS. No native execution or native timing
was repeated. 3D pixels require exact agreement; existing native numerical
comparison tolerances apply elsewhere. No outputs/features were excluded.

Bounded RSS evidence
--------------------

Existing ``MemoryMetric`` samples at a requested 50 ms interval and uses existing
``ChildProcessTerminator`` if aggregate owned controller/server/descendant RSS
exceeds 6144 MiB. A guard trip would stop the entire sequence, never restart or
continue on a new server. The controller only journals the existing samples.
This polling guard is not a kernel-enforced hard allocation ceiling.

There are 6795 retained samples. The greatest observed sample gap is
0.770619 s. Aggregate peak is
4002.011719 MiB; sampled server peak is
2335.167969 MiB. READY server RSS is
962.812500 MiB; final post-job server RSS is
2131.953125 MiB. The first cycles allocate additional memory; the last seven
post-job values range from 2117.882812 to 2210.179688 MiB,
with the final cycle ending below the preceding cycle. This demonstrates a
plateau in this finite window, not infinite-run or full-catalog memory safety.
RSS does not distinguish live retention from allocator high-water capacity.

All raw post-job samples are retained (MiB)::

    Job  Case       Server RSS    Aggregate peak  Values  Science
     1  3D         1466.882812   2757.812500   41  PASS2
     2  Speckles   1561.714844   2862.300781   26  PASS2
     3  Beginner   1690.382812   3189.507812   44  PASS2
     4  3D         1676.960938   3493.238281   41  PASS2
     5  3D         1621.417969   3493.238281   41  PASS2
     6  Speckles   1627.882812   3502.300781   26  PASS2
     7  Beginner   1688.277344   3502.300781   44  PASS2
     8  3D         2017.488281   3568.140625   41  PASS2
     9  3D         2320.007812   4001.980469   41  PASS2
    10  Speckles   2210.019531   4002.011719   26  PASS2
    11  Beginner   2210.164062   4002.011719   44  PASS2
    12  3D         2210.179688   4002.011719   41  PASS2
    13  3D         2118.082031   4002.011719   41  PASS2
    14  Speckles   2117.882812   4002.011719   26  PASS2
    15  Beginner   2130.835938   4002.011719   44  PASS2
    16  3D         2131.953125   4002.011719   41  PASS2

Retaining-owner evidence and limits
----------------------------------

The archived standalone actual production-query reproduction behind #582 proves
that process-wide label/vector/axis/schema caches retain two real label buffers
(1,048,576 bytes) after ``RuntimeValueStore.clear`` and return stale 0.5 after
store replacement with 7.5. The repaired replay immediately returns 7.5 and
releases the label buffers and feature column without a process-cache clear.
Five query/schema cache families, their three keys and the detached dataclass
row cache were removed; existing store-owned revision reuse and call-local
batching remain. Saved production CSV replay checks 936 correlated values.

That proof identifies actual incorrect owners; it does not establish that these
were the sole cause of the historical 13 GiB OOM. The original dominant allocation
and retaining references were not captured. This controlled run is separate
empirical evidence of bounded repeated READY-server execution after the repairs.

Existing wire STATUS excludes ``ExecutionRecord.metadata``. Live byte counts for
record extras and runtime stores are therefore not claimed. Orchestrator-extra
release, worker-store clear and parent diagnostic retention are documented source
laws; public consumed-artifact absence is the actual observed lifetime check.
The sequence preserves retained VALUES, publication and independent image buffers;
it does not change checkpoint/debug retention policies.

Prelaunch RED is retained: the first preparation and launch used different shell
contexts, and the prelaunch source-state guard failed. The subsequent read-only
full comparison differed only in the inherited environment hash; all observed
source/dependency/input/native bytes were unchanged. No server or scientific
job started on that attempt. The successful namespace creates and validates its
complete freeze in the same taskset launch process, without dropping guard fields.

The controlled-repeat acceptance clause in #433 is satisfied. Recommend closing
that bounded functional gate after review while keeping full 30-case scientific,
performance and scaling acceptance open in PR #394. No historical sole-cause,
full-catalog memory guarantee or individual timing gain is asserted.

Retained artifacts
------------------

``qualification.json`` contains exact summary, raw post-job rows and hashes.
``original-evidence.tar.gz`` contains all 6795 RSS samples, all 16 job
receipts/comparisons, original freezes/endpoint records/controller/server logs,
prelaunch RED and original/fixed production-query proofs. Pixel outputs remain in
HOME's owned qualification namespace (482,867,459 bytes), without dataset copies.

Archive SHA-256: ``7ec66003049ae82dcaabe286a525dc7fd725bcc1fbb28679f07a0fa1d9b85d66``.
Source freeze SHA-256: ``ae74357713b962276244810ddf13959565ad38295e954684bc95abb5805a48fd``.
RSS journal SHA-256: ``6488d594fe770328c1545d27688e4de68b732407de79a51e13a65c093d8a7538``.
