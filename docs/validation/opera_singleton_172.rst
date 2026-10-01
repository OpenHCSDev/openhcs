Opera singleton initialization, issue 172
=======================================

Source owner: this implementation branch. Integration, installation, MCP and
merge owner: parent. Base audited: OpenHCS
``5ce9e3087e603aaf5177ea88363ef48a804c1163`` (PR 206 pending at dispatch),
PolyStore gitlink ``91fd7e854ca760a16e7472d8d558b4012e89b6ba``.
Branch: ``fix/opera-singleton-172-20261001``. Worktree:
``/home/ts/wt/openhcs-opera-singleton-172-20261001``.

Boundary and preserved witness
------------------------------

Harmony Index.xml is an external format. The existing OperaPhenixXmlParser
owns stage-coordinate extraction and field remapping. OperaPhenixMetadataHandler
consumes its ``(columns, rows)`` grid and reverses it to ``(rows, columns)``.
No stored format or metadata namespace changes here.

Parent's installed MCP generation (PID 370288) with OperaPhenix, grid 1x1,
tile 64x64, overlap 0, stage error 0, one wavelength, one z level, four cells
and seed 7, without --openhcs-format, emitted
``plate_grid_dimensions_unavailable``. Artifact-plan with complete
``PipelineDocument(pipeline_config=PipelineConfig(), pipeline_steps=[])`` raised
``OperaPhenixXmlContentError: Could not determine grid size from XML data``.

Originals, read-only:
``/home/ts/wt/openhcs-issue-batch-20260929/namespace-installed-20261001/fixtures/raw-opera/Images/Index.xml``
and sibling ``live.stdout`` (generation/compile records at lines 1594-1680).
XML SHA256:
``b3f2c03c8e7b6e7e3196535b934f01f65c7c6b6f6bb22cf6fd6fd308e54db276``.
The XML declares field 1 at finite coordinates (0.000576762, 0.000576762) m.
The base grid reader's ``len(images) > 1`` gate at line 268 rejects this valid
singleton. Colocated channels/planes remain separate singleton groups and fail
the same gate. No original fixture, metadata or live process is modified.

Ownership decision and exact patterns considered
------------------------------------------------

Before edits, read the complete nra-refactoring SKILL.md, local refactor-audit
SKILL.md, current refactor-audit.skill ZIP entrypoint, pattern README, surface
receipt and complete identity, boundaries, implementation and over-time pattern
references. User-supplied standing AGENTS instructions apply; no filesystem
AGENTS.md was found in the owning ancestry or this source tree.

* BOUND-1: duplicated FieldID/PositionX/PositionY raw XML decoding in
  get_grid_size and get_field_positions. Consolidate in the existing parser's
  typed position decoder, used by both consumers; no parallel XML/store owner.
* BOUND-2: considered SourceTileLayout, PolyStore SourceTileGeometry and
  SpatialGridAxis. They own calibrated pixel/projection/runtime geometry, not
  raw Harmony stage coordinates or native field IDs. Do not introduce that
  dependency or a new carrier for this boundary.
* IDEN-6: preserve well/channel/plane grouping, expressed as numeric tuple
  identity rather than an assembled string; do not merge coordinate populations
  across wells or channels to make the singleton work. Field IDs identify fields,
  not grid cardinality. Existing remapping's first-position-per-field contract
  remains distinct from grid grouping.
* IMPL-12 / IMPL-13: collapse duplicate coordinate decoding rather than add a
  third implementation. The existing text helper and parser remain owners.
* IMPL-14: eliminate the 8-term and 6-term anonymous XML admission chains by
  numeric boundary decoding; empty/invalid values remain ineligible.
* TIME-1 / TIME-6: remove the unreachable square/factor field-ID guessing path.
  Nonempty valid coordinate sets already have positive axis cardinalities.
* TIME-5 / TIME-9: no product test switch, fallback reader, alias, cached mutation
  or adapter. Tests load the exact parser source file to avoid microscope package
  discovery and science/native/viewer runtime, and assert that source identity.

Required relation: any nonempty valid stage-coordinate group yields the count
of distinct X and Y positions using the existing 1e-10 m quantization. One point
has one position on each axis. No singleton-specific dispatch is necessary.
Missing, malformed or nonfinite coordinates cannot justify guessed geometry.
Preserve the first multi-image group's existing precedence when a partial
singleton group precedes it; otherwise use the first valid singleton group.

New-case experiment: add a one-field group with 3 channels x 3 planes and field
ID 17; add 1x4, 4x1, 2x3, 3x2 and 3x3 grids with non-contiguous/reversed IDs.
Before: singleton requires a consumer special case; square-ID inference cannot
prove rectangular orientation. After: zero production edits; the existing
coordinate relation and raster remapping handle these external records.

Resource ledger and acceptance boundary
--------------------------------------

Owned disposable scratch:
``/home/ts/.cache/agent-scratch/opera-singleton-172-20261001`` (owner: this
source task; purpose: original traceback, bounded test/AST/guard evidence).
Supervisor bounds each terminal process group to one CPU, 512 MiB RSS,
60 seconds per shard, 256 MiB scratch. Existing Python 3.12.3 for source tests;
existing system Python 3.14.7 for the unchanged CI structural ratchet.
Resource guard before tests: /home 24.3 GiB free, RAM available 20.9 GiB;
warning from historical swap 13.2 GiB. No large job/fleet is started; own
512/256 MiB limits are comfortably within actual safe bounds. No environment,
package, interpreter, native build, JVM, Fiji or science execution is requested.

Focused parser proofs are not a complete NRA scan, public-package import test,
installed MCP acceptance or biological validation. No heavyweight pending scan
is treated as a blocker or as a pass. Original debt guard runs without changes,
waivers, exemptions or metric gaming. Results and archived cleanup follow below.

Executed source proofs at the working checkpoint
-----------------------------------------------

The unchanged original XML fails on the pinned base with its original exception
and succeeds after the patch with grid (1, 1), mapping {1: 1}, fresh-parser
reopen and unchanged SHA256. Negative traceback and negative regression log
are retained. Eleven unittest methods pass, including table-driven singleton,
colocated channels/planes, 1xN, Nx1, rectangular/square geometry, raster mapping,
scope separation, partial-group precedence, external numeric padding,
quantization, invalid/nonfinite coordinates and absent reference fields.
Peak combined RSS: 38.86 MiB for tests, 40.91 MiB for original XML proof;
each shard finishes in less than 0.4 seconds. No limit is hit.

Command from this worktree, with single-thread math and PYTHONDONTWRITEBYTECODE,
under the resource supervisor::

    /home/ts/code/projects/openhcs/.venv/bin/python tests/source_contracts/test_opera_phenix_xml_geometry.py

Only parser source, this test and this receipt are in the source diff. Generator,
filename parser, submodule pins and installed files remain untouched. The parser
change deletes 160 lines and adds 48; deletion is the duplicate coordinate
decoder, admission chains, singleton rejection and unreachable ID guessing,
not a relocation or ratchet exemption.

Separate tracked inventory witness, retained under issue 172
----------------------------------------------------------

Parent observed persisted Opera A01 metadata versus filename-parsed R01C01:
sample succeeds, combined inventory reports two wells. Source witness:
SyntheticMicroscopyGenerator.generate_openhcs_metadata builds
``wells = {well: well for well in self.wells}`` (demo/synthetic_data.py:1124);
OperaPhenixFilenameParser.parse_filename emits RxxCxx (opera_phenix.py:490).
This is generator/catalog versus filename identity, not the stage-coordinate
parser owner. Neither is changed by this fix. Parent retains installed evidence;
issue 172 stays open for normalization through the existing filename declaration
and persisted producer plus installed combined-inventory acceptance. Do not
silently convert the fixture, accept two aliases or fabricate a fallback reader.
