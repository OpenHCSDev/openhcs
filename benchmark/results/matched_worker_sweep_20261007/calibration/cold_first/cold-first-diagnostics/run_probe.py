"""Diagnostic per-assignment wall clocks; never a manuscript capture producer."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

SWEEP = Path(__file__).resolve().parent.parent
ROOT = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else Path(__file__).resolve().parent
ROOT.mkdir(parents=True, exist_ok=True)
AFFINITY = sys.argv[2] if len(sys.argv) > 2 else '0'
ASSIGNMENTS = int(sys.argv[3]) if len(sys.argv) > 3 else 2
TRIALS = int(sys.argv[4]) if len(sys.argv) > 4 else 3
SOURCE = Path('/home/ts/.local/state/openhcs-maintenance/20261004/intensity-batch-maxima-source')
PYTHON = '/home/ts/code/projects/openhcs/.venv-cellprofiler39/bin/python'
original = SOURCE / 'benchmark/native_cellprofiler_batch_worker.py'
code = original.read_text()
replacements = {
    '        observations = []\n': '        observations = []\n        diagnostic_observations = []\n',
    '            assignment_counts = []\n': '            assignment_counts = []\n            diagnostic_assignments = []\n            assignment_boundary = None\n',
    '                    measurements.close()\n': '''                    measurements.close()
                assignment_completed = time.perf_counter()
                assignment_started = clock.pipeline_started if assignment_boundary is None else assignment_boundary
                diagnostic_assignments.append({'assignment': assignment, 'started_monotonic_seconds': assignment_started, 'completed_monotonic_seconds': assignment_completed, 'seconds': assignment_completed - assignment_started})
                assignment_boundary = assignment_completed
            diagnostic_observations.append({'repetition': repetition, 'assignments': diagnostic_assignments})
''',
    '        if request.report_path is not None:\n': "        report['diagnostic_assignment_timings'] = diagnostic_observations\n        if request.report_path is not None:\n",
}
for old, new in replacements.items():
    assert code.count(old) == 1, old
    code = code.replace(old, new)
worker = ROOT / 'instrumented_native_worker.py'
assert not worker.exists(), 'Never overwrite a diagnostic launch'
worker.write_text(code)
compile(code, str(worker), 'exec')
env = dict(os.environ)
native_environment = dict(value.decode().split('=', 1) for value in Path('/proc/1953322/environ').read_bytes().split(b'\0') if value)
for name in ('JAVA_HOME', 'JRE_HOME', 'PATH', 'LD_LIBRARY_PATH'):
    if name in native_environment:
        env[name] = native_environment[name]
temporary = ROOT / 'native_tmp'
temporary.mkdir(exist_ok=False)
env.update(TMPDIR=str(temporary), TMP=str(temporary), TEMP=str(temporary))
env.update(PYTHONPATH=str(SOURCE / 'benchmark'), PYTHONDONTWRITEBYTECODE='1')
for name in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS', 'NUMBA_NUM_THREADS', 'VECLIB_MAXIMUM_THREADS', 'BLIS_NUM_THREADS'):
    env[name] = '1'
metadata = {'status': 'DIAGNOSTIC_NOT_HEADLINE', 'original_worker_sha256': hashlib.sha256(original.read_bytes()).hexdigest(), 'instrumented_worker_sha256': hashlib.sha256(worker.read_bytes()).hexdigest(), 'cpu_affinity': [int(cpu) for cpu in AFFINITY.split(',')], 'numeric_threads': 1, 'assignments': ASSIGNMENTS, 'fresh_trials': TRIALS, 'scope': 'Fresh CP process and loaded pipeline; serial assignments, followed by one additional batch. JVM/process startup excluded from assignment clocks.'}
(ROOT / 'protocol.json').write_text(json.dumps(metadata, indent=2) + '\n')
cases = ('cp4_supplement_combine_objects', 'ExampleIlluminationCorrection_Example3', 'ExampleHuman')
for case in cases:
    for trial in range(TRIALS):
        trial_root = ROOT / case / str(trial)
        trial_root.mkdir(parents=True, exist_ok=False)
        request = json.loads((SWEEP / '1assignment-1worker/capture/cases' / case / 'native_request.json').read_text())
        request.update(output_root=str(trial_root / 'outputs'), report_path=str(trial_root / 'report.json'), repetitions=1, assignment_output_subdirectories=[f'W{i:03d}' for i in range(1, ASSIGNMENTS + 1)])
        assert Path(request['pipeline_path']).is_file() and Path(request['input_dir']).is_dir()
        request_path = trial_root / 'request.json'
        request_path.write_text(json.dumps(request, indent=2) + '\n')
        with (trial_root / 'stdout.log').open('xb') as out, (trial_root / 'stderr.log').open('xb') as err:
            result = subprocess.run(['taskset', '-c', AFFINITY, PYTHON, str(worker), str(request_path)], env=env, stdout=out, stderr=err)
        (trial_root / 'terminal.json').write_text(json.dumps({'returncode': result.returncode}) + '\n')
        if result.returncode:
            print('FAILED', case, trial, flush=True)
            sys.exit(result.returncode)
        report = json.loads((trial_root / 'report.json').read_text())
        print(case, trial, [[round(a['seconds'], 4) for a in r['assignments']] for r in report['diagnostic_assignment_timings']], flush=True)
print('DIAGNOSTIC_TERMINAL_0', flush=True)
