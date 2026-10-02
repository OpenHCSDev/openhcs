Physical-source inspection445 receiving receipt
===============================================

Status and ownership
--------------------

Singer owns the initial read-only BioFormats/inspection RCA and source fixtures
for issue445. Parent owns integration and eventual installed physical-source QA.
Working production checkpoint ``107512352`` is source-qualified and published
in draft446. Installed/native receiving acceptance remains open; issue445 is
addressed, not auto-closed.
This is independent of404's native graph receiving acceptance and440/441's
pending installed receiving acceptance. Planck's live scientific source and
viewer remain untouched.

The existing persistent worktree has an ordinary new branch from main
``3df650bf7faf84f67dbad9acf9ee62a095ab1ecf``. Root394 was checked at
``919fee286f8003a00aafc023ad28767d9713842b``. Its active shared owners include
source bindings, metadata, projection, runtime payloads and materialisation.
No shared394 file is edited by this checkpoint. The source changes below are
limited to the existing public plate inventory and read-only inspection owners;
no Root worktree, environment, package, process or scientific output is changed.
Original untracked134/440 evidence remains intact. No cleanup is authorised.
Root was also checked at current ``a5134a0b85182078700ac06f27dffd3e5788302b``;
neither production path below appears in its shared-file changes. The exact
two-file scope was posted in394 comment5950317703. Qualification is against
main3df650bf7, not a claim about Root's subsequently changing runtime code.

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

The original proposed implementation moved the existing candidate-to-inventory loop
into ``PlateImageInventory.from_source_dataset`` and reuse it from the existing
``from_handler`` path. Read-only ``_image_inventory`` first asks the selected
metadata owner for its exact dataset; if present, use that common constructor.
Otherwise retain the existing virtual-workspace derivation. The generic pipeline
``from_handler`` projection precedence stays unchanged. No BioFormats name/type
branch, new mode, channel roster, selector table, decoder, source receipt or
metadata mutation is necessary. The obsolete inline loop is replaced, not copied.

Working source implementation
------------------------------

Production checkpoint: ``107512352d7af4d9d4f59f539b9440e9143f9144``.
The only changed production files are
``openhcs/core/plate_image_inventory.py`` and
``openhcs/agent/services/plate_inspection_service.py``.
The original full-file R0 rejected the first placement at ``07c216483``:
``PlateInspectionService`` god-class excess increased by8 lines. Its original
measurement remains archived. The actual correction puts the combined read-only
resolution algorithm on existing ``PlateImageInventory.from_read_only_handler``;
the service retains its small dispatch/error-reporting hook. The common
``from_source_dataset`` constructor replaces the old inline candidate loop, and
the generic pipeline/Image Browser ``from_handler`` reuses that constructor
without changing its persisted-projection precedence. Replaced code and the
service's unused projection import are deleted. No parallel source authority is
introduced.

The existing typed request contracts suffice after repair: an explicit
acquisition handler can expose its exact physical planes independently of a
prepared pipeline selection. Query with the original handler declaration
(``microscope_type=bioformats`` for this retained source), select the returned
record's actual channel metadata and exact ``virtual_path``, then use that path
for sample/stream. An auto OpenHCS/workspace query still returns the persisted C1
domain. A physical-container path identifying multiple acquisition planes is
rejected by the unchanged strict record resolver; it is not a channel selector.
There is no new string mode, request selector, channel-specific branch or receipt.

The final five source cases pass. For both three- and four-channel declarations,
preparation persists C1 only; auto inspection/sample and the generic inventory
constructor retain C1. Explicit acquisition inspection returns every declared
plane, exact C3 bounded pixels match the engineering source, and the original
stream source projection plus ``ViewerStreamingSource.load_image`` load exact
C3 pixels with the declared0.5 micrometre calibration. No native viewer is
created. Ambiguous container samples return the original typed failure with no
sample. Persisted metadata remains byte-exact across the whole receiving journey.

An independent ``DeclaredInspectionMetadata`` leaf adds one source-dataset hook
which calls cooperative ``super().source_dataset`` and supplies a new declared
metadata fact. That fact, all four channel addresses and the exact source refs
flow through unchanged generic inventory. No generic consumer, registry or
catalog entry is edited for this case. No genuinely independent new production
capability needs another mixin: existing metadata polymorphism supplies the hook,
and the existing nominal inventory owner supplies the common algorithm.

Final source run:5 PASS,4.87s elapsed, peak240280KiB RSS, zero swap; same
1CPU/512MiB/no-swap/60s kernel limits. Eleven existing inventory, source-ref,
dual stream-record, DTO and path-policy controls passed in the earlier journey
run at the first production placement; those completed controls were not rerun
for ceremony. All tests use source-owned engineering fixtures and existing
read-only dependencies, not scientific input or a new environment.

Three intervening test-harness failures remain retained: an assumed error word
instead of the existing ``matched multiple records`` message; an assumedNone
instead of the DTO's emptytuple failure sample; and an image record passed where
the stream owner requires the unified file record. Only test assertions/record
selection changed for these failures; product guards were not weakened.

Original pinned R0
-------------------

The unchanged original detector at
``/home/ts/wt/openhcs-s1-original-ratchet-20261001``
``3b03785f45df2ef5dc62ba6aed99294192ecbb01`` measured main
``3df650bf7faf84f67dbad9acf9ee62a095ab1ecf`` to production ``107512352``
using ``--root openhcs``. Both actual changed production files are included;
no copied detector, omitted path, increased threshold or positive-delta waiver.
Final exit0,17.82s, peak87628KiB, zero swap. Positive deltas are empty;
the sole nonzero delta is ``PlateInspectionService`` god-class excess minus13.

``physical-source-inspection-445-source-20261002.tar.gz`` contains byte-exact
``original.log``, ``repair.log``, ``final.log``, ``journey.log``,
``qualified.log``, ``owner-final.log``, ``r0.log`` and ``r0-final.log``.
The original smaller archive and loose originals remain retained. Original log
whitespace is not rewritten or represented as production diff cleanliness.
Final archive SHA256:
``ffc8001ed2d76c43626f6154f84b06fa54a4b1865f209ab4a00212d9b6ccef8a``.

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

The bounded source requirements above are qualified. Parent still owns the
installed public original-C1/C3 matched raw/composite and
nuisance QA journey. No installed, native or biological readiness is claimed.
