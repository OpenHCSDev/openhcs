# Issue257 runtime extension composition checkpoint

Implementation/file owner: Socrates, PR262/issues257+264. Parent owns integration
and installed/native acceptance; Zeno owns issue265 path_planner main-flow/
lineage arguments. Lovelace owns R0/PR263. No config/compiler/path_planner or
archive surface change is included. No separate archive S-surface worker has
been verified here. Coordinate with Zeno before any heavy/native slot use.

## Retained actual failure

Parent's source82 two-step journey, execution
`2f15f508-d405-48f1-9ce3-35ae1ae314e1`, terminated FAIL after114.77s.
First-step main/checkpoint TIFF, CSV and ROI ZIP publication was partial
evidence, not complete257 acceptance. Second-step lineage failed separately
under265. No original request or job was replayed.

Original journey:
`/home/ts/wt/openhcs-issue-batch-20260929/source-live-publication-262-20260930/journey.json`
SHA256 `78dd804803d6da58856d180a6baed50d2c3e50b4ecbf68f9a76553df7f605745`.

The first-step filename still duplicated its source address:
`checkpoints_step0/image.ome.tif_s001_w1_z001_t001_fixture_image.ome.tif_s001_w1_z001_t001.tif`.
Its retained extension was incorrectly
`.ome.tif_s001_w1_z001_t001.tif`, even though the real source-schema parser
resolves the source filename extension as `.tif`.

## Existing-owner correction

Delete the composer's all-`Path.suffixes` extension invention, with no replacement
guess in a factory/adapter. STACK consensus and BUNDLE projection retain
actually declared component metadata; missing extension remains absent.

The materializer's existing parser-backed source-stem authority now reads
`SourceImageIdentity.filename_extension`, or resolves absent source facts through
its existing `with_parsed_path_components(self.parser)` boundary. It no longer
joins all source-path suffixes. Unparseable sources without a declaration do not
acquire an extension. Real declared compound `.ome.tif` remains authoritative.

Product delta:7 added/20 deleted lines in two methods. No new parser/regex,
registry, store, compatibility route, protocol change or legacy repair.
`SourceComponentMetadataStemAuthority.required_extension` and intentional
semantic-omission guards are unchanged. Wrong factory-produced metadata is
removed at its producer, not sanitized after consumers preserve it.

NRA/refactor-audit declaration-owner and derived-view constraints influenced
this deletion and reuse. Current authoritative archive SHA256:
`100fbe8ef89664b866777e87b2c8640a3432e8a10e9188dff81c97942d551bf6`.
No full NRA/ratchet scan or archive surface refactor is claimed.

## Source evidence

Real `SourceSchemaFilenameParser` -> runtime metadata composition -> typed
named-output identity/path -> ordinary image materializer, not Fake/DotParser.
Sixteen family cases cover plain/dotted wells, `.tif`/`.ome.tif`, declared/
parser-resolved extension, and STACK/BUNDLE. The named output uses the actual
`fixture_image` qualifier and requires the source coordinate marker exactly
once. Three further cases cover direct dotted parser resolution and no invented
extension on an unparseable source. All pixels are tiny new synthetic fixtures.

Corrected pre-product-change red:6 failed/4 passed/13 deselected. The initial
fixture also had four test-author errors from retaining a consumed plane axis;
the fixture was corrected to `for_leading_source_plane(0)`, not the runtime
guard weakened.

Current regression checkpoint:112 passed in four bounded groups:
47 provenance/persistence/257/264,6 image/ROI materializers,16 runtime identity/
stack,43 produced inventory/projection. One spawned-process test was excluded.
After aligning the qualifier with the native example, the32-test changed module
passed again. Two known asyncio configuration warnings arise from deliberately
disabled plugin autoload. Formatting and `git diff --check` pass.

Tests used the existing Python, one CPU/native thread,55s shell timeout,
`--noconftest`, no pytest cache, and the existing ABI import solely for collection.
No native execution server/JVM/MCP/GUI/build/install/download/heavy test ran.
Original source receipt and AST reproducer remain byte-identical; their hashes
and exact test summaries are in the companion JSON receipt.

## Acceptance still required

Parent's fresh native control must establish exact marker-once filenames,
CSV typed address, exactly one ROI in every ZIP, complete disk projection TIFF
coverage with extension/address, and typed MCP inventory with full result
readback; include images/labels/artifacts and the dotted-OME chained control
after265 is integrated. Original partial readback is not full acceptance.
No readiness/merge/install/live success claim follows from112 source tests.
