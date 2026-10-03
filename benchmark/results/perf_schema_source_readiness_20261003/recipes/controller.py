"""Ordinary public ABBA; only three owned source files vary between terminated runs."""
import csv
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

HERE = Path(__file__).parent
SOURCE = Path('/home/ts/code/projects/openhcs-shared-runtime-plumbing')
MAIN = Path('/home/ts/code/projects/openhcs')
PYTHON = MAIN / '.venv/bin/python'
CASE = 'ExampleIlluminationCorrection_Example3'
VARIANTS = json.loads((HERE / 'variants.json').read_text())

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

ordinary = load('ordinary_schema_source', '/tmp/run_integrated_fields_ordinary_abba_20261002.py')
base = load('schema_source_inputs', '/var/tmp/run_narrow450_runtime_phase_probe_20261002.py')
base.SOURCE = SOURCE
base.CASES = (CASE,)
sparse = load('schema_source_sparse', '/var/tmp/openhcs_measurement_sparse_inventory_v2_20261003.py')

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args], text=True).strip()

def environment():
    env = ordinary.environment(SOURCE)
    for key in tuple(env):
        if key.startswith(('OPENHCS_DIAGNOSTIC_', 'OPENHCS_CAPTURE_CELLPROFILER_FIXTURES_', 'OPENHCS_PROFILE_FUNCTION_RUNTIME')) or key == 'OPENHCS_WORKER_PROFILE_DIR':
            del env[key]
    env.update(PYTHONDONTWRITEBYTECODE='1', TMPDIR=str(HERE / 'tmp'))
    return env

def sources():
    dependencies = {}
    for line in git(SOURCE, 'config', '--file', '.gitmodules', '--get-regexp', 'path$').splitlines():
        _, relative = line.split(maxsplit=1)
        repo = SOURCE / relative
        dependencies[relative] = {'head': git(repo, 'rev-parse', 'HEAD'), 'status': git(repo, 'status', '--porcelain'), 'files': base.tracked_source_hashes(repo)}
    return {'head': git(SOURCE, 'rev-parse', 'HEAD'), 'status': git(SOURCE, 'status', '--porcelain'), 'files': base.tracked_source_hashes(SOURCE), 'dependencies': dependencies,
            'native_binaries': {r: sha(SOURCE/r) for r in ordinary.NATIVE}}

def select(label):
    # This checkout is owned, and the source files are not being edited by agents.
    # No live server may remain while its source is changed.
    for entry in VARIANTS:
        target = Path(entry['path'])
        assert target.is_relative_to(SOURCE)
        current = sha(target)
        assert current in {sha(entry['A']), sha(entry['B'])}, 'Unexpected source edit'
        target.write_bytes(Path(entry[label]).read_bytes())

def assert_endpoint_terminal(receipt):
    import psutil
    endpoint = receipt['endpoint_provenance']
    pid = endpoint['endpoint_pid']
    try:
        process = psutil.Process(pid)
        assert abs(process.create_time() - endpoint['endpoint_create_time_epoch_seconds']) > 0.1 or not process.is_running() or process.status() == psutil.STATUS_ZOMBIE, 'Measured endpoint remains live'
    except psutil.NoSuchProcess:
        pass

def main():
    assert shutil.disk_usage('/var/tmp').free >= 512 * 1024**2
    assert shutil.disk_usage('/home').free >= 2 * 1024**3
    assert not (HERE / 'freeze.json').exists()
    (HERE / 'tmp').mkdir()
    env = environment()
    original = sources()
    assert not original['status'], 'Commit source before measurement'
    physical = base.physical_input_hashes()
    sparse_state = sparse.sparse_source_inventory(SOURCE)
    installed = subprocess.check_output([str(PYTHON), '-I', '-m', 'pip', 'freeze', '--all'], text=True)
    imports = subprocess.check_output([str(PYTHON), '-c', 'import openhcs,objectstate,python_introspect,json;print(json.dumps({m.__name__:m.__file__ for m in (openhcs,objectstate,python_introspect)}))'], env=env, cwd=str(HERE/'tmp'), text=True)
    for path in json.loads(imports).values():
        assert Path(path).is_relative_to(SOURCE), path
    freeze = {'candidate': original, 'physical_inputs': physical, 'sparse_inventory': sparse_state, 'installed_freeze': installed, 'python_sha256': sha(PYTHON.resolve()), 'controller_sha256': sha(__file__), 'environment': env, 'imports': json.loads(imports),
              'variants': [{**r, 'A_sha256': sha(r['A']), 'B_sha256': sha(r['B'])} for r in VARIANTS],
              'scope': 'Four ordinary uninstrumented public Illumination runs ABBA, CPU5 1w_1t INLINE, default OUTCOMES and memory observer. Server READY preparation/startup and shutdown excluded. A is exact prior source bytes for three files; dependency Git HEADs identify containing checkout, file hashes identify actual baseline contents. Only source lookup, existing registered type projection and registry readiness differ. No scientific processing or numerical changes. No new native CP execution.'}
    (HERE/'freeze.json').write_text(json.dumps(freeze, indent=2)+'\n')
    rows = []
    lock = Path('/tmp/openhcs-benchmark-xdg-cache/openhcs/official30-runtime.lock')
    lock.parent.mkdir(parents=True, exist_ok=True)
    try:
        with lock.open('a+') as lease:
            fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
            for index, label in enumerate(('A', 'B', 'B', 'A')):
                select(label)
                before = sources()
                dest = HERE / f'{index}-{label}'
                assert not dest.exists()
                command = ['/usr/bin/taskset', '-c', '5', str(PYTHON), '-c', ordinary.BOOTSTRAP, str(SOURCE/'scripts/benchmark_cppipe_well_throughput.py'), '--manifest', str(SOURCE/'benchmark/manifests/official30_portable_axis1.json'), '--mode', '1w_1t', '--case', CASE, '--output-dir', str(dest/'public')]
                record = {'index': index, 'label': label, 'source': before, 'command': command}
                (HERE/f'{index}-{label}-source.json').write_text(json.dumps(record, indent=2)+'\n')
                print(json.dumps({'status': 'RUNNING', 'index': index, 'label': label}), flush=True)
                started = time.monotonic()
                with (HERE/f'{index}-{label}.log').open('x') as stream:
                    result = subprocess.run(command, cwd=str(HERE/'tmp'), env=env, stdout=stream, stderr=subprocess.STDOUT, timeout=900)
                assert sources() == before, 'Source/dependency/native bytes changed during run'
                assert base.physical_input_hashes() == physical
                assert subprocess.check_output([str(PYTHON), '-I', '-m', 'pip', 'freeze', '--all'], text=True) == installed
                assert sha(__file__) == freeze['controller_sha256']
                measured = list(csv.DictReader((dest/'public/well_throughput.csv').open()))
                assert result.returncode == 0 and len(measured) == 1 and measured[0]['status'] == 'success' and measured[0]['successful_wells'] == '1' and measured[0]['execution_route'] == 'ordinary-zmq-outcomes-v1'
                receipt_path, = (dest/'public'/CASE/'wells_1/workers_1/ordinary_run_evidence').glob('*/measured_pipeline_receipt.json')
                receipt = json.loads(receipt_path.read_text())
                assert receipt['observation_export_scope'] == 'outcomes' and receipt['observed_axis_count'] == receipt['expected_axis_count'] == 1
                assert_endpoint_terminal(receipt)
                assert sum(p.stat().st_size for p in dest.rglob('*') if p.is_file()) < 128 * 1024**2, 'Output cap'
                rows.append({'label': label, 'directory': str(dest), 'seconds_including_startup_for_audit_only': time.monotonic()-started, 'public_rows': measured, 'receipt': str(receipt_path), 'receipt_sha256': sha(receipt_path), 'source_freeze_sha256': sha(HERE/f'{index}-{label}-source.json')})
                (HERE/'observations.json').write_text(json.dumps({'rows': rows, 'science': 'PENDING', 'scope': freeze['scope']}, indent=2)+'\n')
                print(json.dumps({'status': 'RUN_COMPLETE', 'label': label, 'timings': {k: measured[0][k] for k in ('compile_seconds', 'execute_seconds', 'total_seconds')}}), flush=True)
    finally:
        select('B')
    assert sources() == original
    sparse.validate_sparse_source_inventory(SOURCE, sparse_state)
    from statistics import mean
    means = {label: {key: mean(float(row[key]) for r in rows if r['label']==label for row in r['public_rows']) for key in ('compile_seconds', 'execute_seconds', 'total_seconds')} for label in ('A', 'B')}
    result = {'means': means, 'saved_seconds': {key: means['A'][key]-means['B'][key] for key in means['A']}, 'rows': rows, 'science': 'PENDING', 'scope': freeze['scope']}
    (HERE/'observations.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': 'ABBA_MEASUREMENT_COMPLETE_SCIENCE_PENDING', 'means': means, 'saved_seconds': result['saved_seconds']}), flush=True)

if __name__ == '__main__':
    main()
