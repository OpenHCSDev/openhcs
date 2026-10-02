Physical-source inspection445 receiving receipt
===============================================

Status and ownership
--------------------

Singer owns the initial read-only BioFormats/inspection RCA and source fixtures
for issue445. Parent owns integration and eventual installed physical-source QA.
This is independent of404's native graph receiving acceptance and440/441's
pending installed receiving acceptance. Planck's live scientific source and
viewer remain untouched.

The existing persistent worktree has an ordinary new branch from main
``3df650bf7faf84f67dbad9acf9ee62a095ab1ecf``. Root394 was checked at
``919fee286f8003a00aafc023ad28767d9713842b``. Its active shared owners include
source bindings, metadata, projection, runtime payloads and materialisation.
No shared394 file is edited by this checkpoint. The proposed changes below are
limited to the existing public plate inventory and read-only inspection owners;
no Root worktree, environment, package, process or scientific output is changed.
Original untracked134/440 evidence remains intact. No cleanup is authorised.

Retained installed witness
--------------------------

The full reproducer is
``/home/ts/wt/openhcs-issue-batch-20260929/carrier434-installed-20261002/C3-PHYSICAL-READ-BOUNDARY.rst``.
The author's exact requests are retained under
``/home/ts/wt/openhcs-issue-batch-20260929/rbpms-r0010-development-434-20261002/output``:
``CANDIDATE05-C3-READONLY-QA.rst``,
``CANDIDATE05-C3-READONLY-EVIDENCE.json`` and
``mcp-continuation03.stdin/stdout/timing``.

Source metadata declares C1 AF647-T1, C2 AF488-T2 and C3 H3258-T3.
Ordinary and explicit BioFormats queries expose only the pipeline-bound C1;
an explicit physical-container sample also resolves C1. This is missing safe
original-channel QA access, not evidence of a channel swap. Only engineering
receipts, request schemas and metadata identities were inspected. No CZI,
scientific array values, ROI geometry or held-out/reference input was opened.

Existing owner boundary
------------------------

``PlateInspectionService._image_inventory`` reads the persisted virtual-workspace
projection before ``PlateImageInventory.from_handler`` considers the metadata
owner's exact ``source_dataset``. A nonempty persisted C1 projection therefore
suppresses the fresh explicit BioFormats owner's physical C2/C3 candidates.
The query/sample/stream DTOs have no separate physical-plane selector.

The required relation is not to widen the pipeline source set: a read-only
explicit acquisition handler must be able to inventory its own exact declared
planes independently of an already prepared workspace. The automatically selected
OpenHCS workspace owner must still expose the persisted C1 selection. Sampling
a returned exact virtual record must use its original ``SourcePixelRef``;
one container path shared by several planes must not silently select one plane.

Proposed narrow implementation: move the existing candidate-to-inventory loop
into ``PlateImageInventory.from_source_dataset`` and reuse it from the existing
``from_handler`` path. Read-only ``_image_inventory`` first asks the selected
metadata owner for its exact dataset; if present, use that common constructor.
Otherwise retain the existing virtual-workspace derivation. The generic pipeline
``from_handler`` projection precedence stays unchanged. No BioFormats name/type
branch, new mode, channel roster, selector table, decoder, source receipt or
metadata mutation is necessary. The obsolete inline loop is replaced, not copied.

NRA and catalog review
-----------------------

The current NRA skill and authoritative refactor-audit archive were read.
BOUND-8 applies where the richer acquisition candidate domain is hidden behind
the persisted pipeline projection. BOUND-2 prohibits bypassing the typed
``SourceCandidate``/``SourcePixelRef`` owners. MEMB-1/2 prohibit a separate
physical-channel catalog. IMPL-12/13 prohibit another candidate converter or
sampling mechanism. A future exact source dataset supplied by another metadata
declaration must work without a concrete generic-consumer branch. No independent
production capability requires ornamental multiple inheritance.

Original bounded source checkpoint
------------------------------------

``tests/unit/agent/test_physical_source_inspection_445.py`` extends the existing
BioFormats manifest fixture to a tiny three-channel NPY-backed container.
It uses the real ``PlateInspectionService``, ``BioFormatsHandler``, durable
workspace preparation, inventory and storage sampler. A nominal
``PlateInspectionFileManagerFactory`` leaf supplies only the real disk backend;
there is no JVM, Fiji, optional backend preparation, native viewer or provider.

Original main: two controls PASS, required post-preparation C3 access RED:
``observed_channels=[1], total_count=1``. Before preparation, both three- and
four-channel declarations expose and sample C3 exactly; no generic consumer
edit is needed for the fourth channel. The C1-only persisted source domain and
sample are checked, and metadata remains byte-exact even when the red assertion
fails. This is source-boundary proof, not live scientific acceptance.

Kernel scope: MemoryMax512MiB, MemorySwapMax0, CPUQuota100%, one CPU affinity,
external60s timeout, plugin/provider-free. Elapsed4.60s, peak240972KiB RSS,
zero swap. Pytest's two plugin-disabled configuration warnings are retained.
The byte-exact first log is archived in
``physical-source-inspection-445-original-20261002.tar.gz`` and remains loose
under owned ``.qa445-physical-source-20261002/original.log``.

Receiving acceptance still required
------------------------------------

After source repair: explicit physical inventory must return exact C3 and its
bounded sample; auto/workspace C1 and persisted metadata must be unchanged;
ambiguous physical-container sampling must fail rather than choose C1 silently.
Existing inventory, path-policy and sampling bounds must remain strict.
Parent later owns the installed public original-C1/C3 matched raw/composite and
nuisance QA journey. No installed, native or biological readiness is claimed.
