"""Strict complete authored image inventory and retained native input qualification."""
import openhcs
from pathlib import Path
import hashlib
import json

from benchmark.adapters.openhcs import _strict_cellprofiler_runtime_equivalence_policy
from benchmark.matched_cellprofiler_batch import _require_compared_output_inventory
from openhcs.core.equivalence.comparison import runtime_image_differences, runtime_table_differences
from openhcs.core.equivalence.outputs import RuntimeOutputSnapshot
from openhcs.core.runtime_exports import RuntimeExportObservation
from openhcs.core.virtual_workspace_metadata import METADATA_CONFIG, VirtualWorkspaceSourceProjectionEntries
from openhcs.core.source_projection import SourceProjectionSet

HERE = Path(__file__).parent
REFERENCE = HERE.parent/'illumination-compiler-ledger-v4'
REFERENCE_SCIENCE = HERE.parent/'illumination-compiler-ledger-v4-science.json'
NATIVE = Path('/var/tmp/openhcs-current-illumination3-native-timing-science-v1-20261002.json')
CASE = 'ExampleIlluminationCorrection_Example3'

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def read(directory):
    receipt_path, = (directory/'public'/CASE/'wells_1/workers_1/ordinary_run_evidence').glob('*/measured_pipeline_receipt.json')
    receipt = json.loads(receipt_path.read_text())
    assert receipt['observation_export_scope'] == 'outcomes'
    assert receipt['observed_axis_count'] == receipt['expected_axis_count'] == 1
    assert sha(receipt['observation_export_path']) == receipt['observation_export_sha256']
    assert sha(receipt['results_summary_path']) == receipt['results_summary_sha256']
    root, = map(Path, receipt['output_roots'])
    assert root.resolve().is_relative_to(directory.resolve())
    files = frozenset(p for p in root.rglob('*') if p.is_file())
    exports = RuntimeExportObservation.from_output_roots((root,))
    snapshot = RuntimeOutputSnapshot.from_export_observation(exports, source_workspaces=(root,))
    return receipt_path, receipt, root, files, exports, snapshot

def main():
    assert not (HERE/'science.json').exists()
    obs = json.loads((HERE/'observations.json').read_text())
    assert len(obs['rows']) == 4 and [r['label'] for r in obs['rows']] == ['A','B','B','A']
    qualification = json.loads(REFERENCE_SCIENCE.read_text())
    assert qualification['status'] == 'CURRENT_BB9_DIAGNOSTIC_FULL_AUTHORED_IMAGE_INVENTORY_BYTE_NATIVE_INPUT_TRANSITIVE_PASS'
    native = json.loads(NATIVE.read_text())
    assert native['status'] == 'PASS_AUTHORED_NONEMPTY_SAVED_IMAGE_SCIENCE_AND_MATCHED_FRESH_NATIVE_TIMING'
    for role in ('native_report','source_environment_input_witness','saved_image_science_receipt'):
        assert sha(native[role]) == native[role+'_sha256']
    ref = read(REFERENCE)
    assert sha(ref[0]) == qualification['current_receipt_sha256']
    assert {str(p.relative_to(ref[2])): sha(p) for p in ref[3] if p.suffix == '.npy'} == qualification['scientific_npy_bytes']
    before = {str(p): sha(p) for p in ref[3]}
    policy = _strict_cellprofiler_runtime_equivalence_policy()
    results = []
    freeze = json.loads((HERE/'freeze.json').read_text())
    cpp = freeze['physical_inputs']['cppipe_path']
    assert cpp['path'] == native['source_cppipe'] and list(cpp['files'].values()) == [native['source_cppipe_sha256']]
    environments = []
    for run in obs['rows']:
        actual = read(Path(run['directory']))
        assert sha(actual[0]) == run['receipt_sha256']
        before.update({str(p): sha(p) for p in actual[3]})
        td = runtime_table_differences(ref[5].tables, actual[5].tables, policy)
        im = runtime_image_differences(ref[5].images, actual[5].images, policy)
        assert not td and not im, (td, im)
        assert not actual[5].tables and len(actual[5].images) == len(ref[5].images) == 2
        _require_compared_output_inventory(reference_files=ref[3]-frozenset(METADATA_CONFIG.managed_paths(ref[2])), candidate_files=actual[3], reference_exports=ref[4], candidate_exports=actual[4], reference_snapshot=ref[5], candidate_snapshot=actual[5], candidate_managed_files=frozenset(METADATA_CONFIG.managed_paths(actual[2])))
        images = {str(p.relative_to(actual[2])): sha(p) for p in actual[3] if p.suffix == '.npy'}
        assert images == qualification['scientific_npy_bytes'] and len(images) == 2
        workspace = Path(actual[1]['execution_plate_id'])
        subdirs = json.loads((workspace/'openhcs_metadata.json').read_text())['subdirectories']
        entries = tuple(entry for s in subdirs.values() for entry in VirtualWorkspaceSourceProjectionEntries.from_subdirectory(s).entries.values())
        projections = SourceProjectionSet(entries)
        assert len(projections.plane_projections) == 1 and not projections.artifact_projections
        assert all(not p.ref.source_axis_indices for p in projections.plane_projections)
        selected = {str(Path(p.ref.backend_address).resolve(strict=True)): sha(p.ref.backend_address) for p in projections.plane_projections}
        assert selected == native['physical_source_sha256']
        assert actual[1]['global_config_source_sha256'] == ref[1]['global_config_source_sha256']
        assert actual[1]['endpoint_provenance']['client_openhcs_file'] == str(Path(freeze['imports']['openhcs']))
        environments.append(actual[1]['server_environment'])
        results.append({'label': run['label'], 'directory':run['directory'], 'receipt_sha256':sha(actual[0]), 'scientific_npy_bytes':images, 'physical_selected_inputs':selected, 'image_differences':im, 'table_differences':td, 'full_physical_inventory':'PASS'})
    assert all(e == environments[0] for e in environments)
    assert all(sha(p) == digest for p,digest in before.items())
    result = {'status':'ALL4_ORDINARY_AUTHORED_IMAGES_EXACT_AND_RETAINED_NATIVE_INPUT_PARITY_PASS', 'runs':results, 'means':obs['means'], 'saved_seconds':obs['saved_seconds'], 'all_before_after_output_sha256':before, 'server_environment':environments[0], 'freeze_sha256':sha(HERE/'freeze.json'), 'reference_science_sha256':sha(REFERENCE_SCIENCE), 'native_receipt_sha256':sha(NATIVE), 'validator_sha256':sha(__file__), 'limits':['Two observations per variant; no execution speedup is claimed.', 'Authored workload exports two images and no tables.', 'Native comparison is retained matched CP4.2.8.1 evidence, not a fresh native run.', 'Ordinary pipeline total excludes mandatory server startup and shutdown.']}
    (HERE/'science.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status':result['status'], 'means':obs['means'], 'saved_seconds':obs['saved_seconds'], 'science_sha256':sha(HERE/'science.json')}))

if __name__ == '__main__':
    main()
