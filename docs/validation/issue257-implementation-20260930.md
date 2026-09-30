# Issue257 implementation checkpoint

Implementation/file owner: this agent. Integration owner: parent/OpenHCS
coordinator. This supersedes the investigation-only ownership at `ae6c90b6d`.

Source-only means product edits and bounded fixture tests are authorized; no
native execution server, JVM, MCP, GUI, heavy suite, package/build/install,
scientific input or held-out/reference data is authorized here. Zeno retains
the source-live slot. Frozen H002B files remain untouched.

## Implemented owners

Working draft: https://github.com/OpenHCSDev/openhcs/pull/262, first product
checkpoint `ddca5e7cb95419d275f818ab8fa20b016cb0d6eb`. Latest source evidence:
28 publication/stack tests pass in2.81s;15 existing identity/stack tests pass
in2.46s;15 projection/architecture tests pass in0.90s. Total58. The added cases
cover reordered dotted stacks, atomic missing-address rejection and pruning
deleted images from all three projection fields and component coverage.
The24-test result below is the earlier checkpoint, not the latest total.

Existing ABI SHA256:
`d0051154f8af59874004373603aabff0ae0576216c48076e1470d6569bb18b88`.

R0/L0/S1–S8 does not expand this bug PR's scope. Lovelace owns R0 CI; hosted
CI is not a wait condition.264 is now combined through the same declared
source-extension owner; see `issue264-source-extension-20260930.md` for cause,
current93-test source checkpoint and remaining native acceptance. The58-test
result above is the earlier257 checkpoint, not an installed-readiness claim.

- `FunctionOutputIdentity.filename_values` owns storage coordinates, separate
  from semantic components; inherited `filename_address` projects them through
  `OpenHCSPlaneAddress` without reading a generated filename.
- `FunctionOutputExtensionAuthority` honors retained extension metadata before
  source-path decoding; canonical external paths use the existing parser/cache
  declaration. Physical source names use their terminal suffix, not every dot
  in their identity. All four source-metadata sites and the stacked fallback
  site use this authority.
- `FunctionOutputPathAuthority` qualifies before the bound, normalized parser
  extension, not the complete `Path.suffixes` chain. It does not parse its output.
- `OutputTarget.produced_projection_metadata` publishes record-owned addresses,
  retaining saved header/dtype/calibration, semantic source components and
  artifact aliases. Its filename parser call is deleted.
- `AtomicMetadataWriter.publish_source_projection_metadata` merges the existing
  durable source-projection store and publishes the saved image inventory in
  one transaction. Reconciliation after memory cleanup uses those typed durable
  projections. During step publication, concurrent foreign files await their
  own producer publication; final reconciliation requires complete typed
  coverage and prunes deleted target images. Other-directory artifacts remain.
  There is no filename or input-cache fallback, new store or protocol format.
- `SourceProjectionMetadataSerializer.component_metadata` is the shared
  declaration-derived inventory projection. Input display labels cannot add
  component keys. The generated-output route no longer invokes the disk
  generator's filename-inventory parser; external discovery still owns parsing.

NRA/refactor-audit constraints applied: BOUND-2/4, IDEN-1/5, TIME-9. This is
source-traced coverage, not a global NRA scan or correctness certificate.

## Source fixture evidence and limits

Original failure reproducer and JSON receipt remain byte-identical to
`ae6c90b6d`; the receipt is historical, not a receipt for changed source. Run
that old probe against its original source revision, not the new signatures.

Initial selected `test_function_outputs.py` tests: **24 passed, 31 deselected** in
2.60s. Includes 18 parameterized publication/readback fixtures for plain,
dotted and OME-named wells, two declared extensions, and complete/reordered/
reduced Z coverage. Their parser is made to raise during publication; final
reconciliation runs after memory image removal. Existing aliases, collapsed
semantics, unknown layout and multi-axis completion checks are included.

The later-axis fixture now supplies that axis's real typed producer publication
before final reconciliation, rather than inventing a file without a record and
expecting the reconciler to infer its coordinates from its name. Its pixels
are already present at the first axis publication, exercising the concurrent
ownership interval without inventing their address or pruning their record.

Command environment: `PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 OPENHCS_CPU_ONLY=true
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1`; actual existing
`/home/ts/code/projects/openhcs/.venv/bin/python -B`; shell timeout55s;
pytest `--noconftest -p no:cacheprovider -q --tb=short`. Disabling global conftest
avoids viewer/process cleanup fixtures and GUI plugins.

Collection initially failed because the isolated source tree lacks its built
`_tabular_native` module. Without building/installing/copying anything, subsequent
source fixtures explicitly preloaded the already-installed
`/home/ts/wt/openhcs-custom-function-admission-20260929/openhcs/core/_tabular_native.abi3.so`
via `importlib.util.spec_from_file_location`. Its C++ source is unchanged between
installed86 and the32d source base. This is an existing ABI import, **not a
native worker/execution-server launch or installed-entrypoint acceptance**.
All changed Python owners are imported from this isolated source tree.

Intermediate fixture failures retained in this record: the first implementation
run had21 failures/3 passes due to using absent `FIELDS.MAIN` (corrected to the
serializer's declared field); the next had18 failures/6 passes due to the new
test attempting nonempty memory-directory deletion (corrected to explicit
fixture-file deletion). The voxel-spacing assertion uses its actual declared
`values_zyx` field. No assertion was weakened. Two pytest configuration warnings
are expected with automatic plugin loading disabled (asyncio config options).

`git diff --check` passes. No native compile/execute journey, installed readiness,
or biological correctness is claimed. Parent integration must perform the tiny
synthetic native acceptance after the live slot is available, with image
publication enabled, first/chained lineage and image-plus-artifact outputs.

## Current runtime-composition follow-up

The actual source82 native control retained a factory-created dotted-well
extension and duplicated the source address. This is not complete257
acceptance. The current same-owner correction deletes the composer suffix
guess and derives materializer extension candidates from SourceImageIdentity
and its existing parser boundary. Product delta is7 added/20 deleted lines;
strict omission/extension guards remain unchanged.112 bounded source tests
pass, including the real source-schema/composer/materializer family. The
original receipts above remain historical and unchanged. Full current
root-cause, source red/green and parent acceptance requirements are in
`issue257-runtime-composition-20260930.md` and its companion JSON receipt.
Zeno owns265 path_planner lineage; Lovelace owns R0. Parent owns integration
and the fresh finite native control; no native slot was used here.

## Reproducible bounded command

Run from this worktree, with the environment/timeout above:

```python
import importlib.util, sys, pytest
name = "openhcs.core._tabular_native"
spec = importlib.util.spec_from_file_location(
    name,
    "/home/ts/wt/openhcs-custom-function-admission-20260929/openhcs/core/_tabular_native.abi3.so",
)
module = importlib.util.module_from_spec(spec)
sys.modules[name] = module
spec.loader.exec_module(module)
raise SystemExit(pytest.main([
    "--noconftest", "-p", "no:cacheprovider", "-q", "--tb=short",
    "tests/unit/test_function_outputs.py", "-k",
    "produced_address_publication or produced_projection_metadata_persists_typed_collapsed_semantics "
    "or produced_projection_derives_artifact_alias or completed_plate_metadata "
    "or metadata_writer_preserves_unknown_layout",
]))
```
