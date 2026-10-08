"""Finish actual8, then capture only OpenHCS; archive each qualified mode serially."""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

SWEEP = Path('/home/ts/.local/state/openhcs-maintenance/20261007/issue1100-matched-sweep-v1')
WORKTREE = Path('/home/ts/code/projects/openhcs-cohort-qualification-main429-20261002')
RECORD = WORKTREE / 'benchmark/results/matched_worker_sweep_20261007'
PYTHON = '/home/ts/code/projects/openhcs/.venv/bin/python'
PLAN = RECORD / 'protocol/v2/protocol-manifest.json'
CONVERTER = RECORD / 'protocol/v2/convert_matched_reports.py'
ARCHIVER = RECORD / 'protocol/v2/archive_converted_modes.py'
RENDERER = RECORD / 'protocol/render_sweep.py'

def load(path):
    return json.loads(path.read_text())

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def preserve(source, target):
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        assert sha(target) == sha(source), (source, target)
    else:
        target.write_bytes(source.read_bytes())
    assert sha(target) == sha(source)

def harness_script(script, *arguments):
    # Overlay the benchmark package only; production remains the frozen source.
    bootstrap = (
        'import sys;'
        'sys.path.insert(0,"/home/ts/.local/state/openhcs-maintenance/20261004/intensity-batch-maxima-source");'
        'import benchmark,runpy;'
        f'benchmark.__path__={[str(WORKTREE / "benchmark")]!r};'
        'sys.argv=sys.argv[1:];runpy.run_path(sys.argv[0],run_name="__main__")'
    )
    return ['taskset', '-c', '0', PYTHON, '-B', '-c', bootstrap, str(script), *arguments]

def run(argv, **kwargs):
    subprocess.run(argv, cwd=WORKTREE, check=True, **kwargs)

plan = load(PLAN)
assert plan['status'] == 'PREPARED_REVISED_CAPTURE_PROTOCOL'
assert sha(CONVERTER) == plan['converter_sha256']
assert sha(ARCHIVER) == plan['archive_owner_sha256']
assert sha(RENDERER) == plan['render_owner_sha256']
actual8 = SWEEP / '8assignments-2workers/capture'
print('WAITING_FOR_ACTUAL8', flush=True)
while not (actual8 / 'terminal.json').exists():
    time.sleep(30)
assert load(actual8 / 'terminal.json')['returncode'] == 0
while not (actual8.parent / 'converted/summary_custody.json').exists():
    time.sleep(5)
assert load(actual8.parent / 'converted/summary_custody.json')['status'] == 'PASS'

# Let the original qualifier finish its current archive, then prevent it from
# attempting its obsolete actual-target native admission on future modes.
watcher = 1330152
while Path(f'/proc/{watcher}').exists():
    children = subprocess.run(['ps', '-o', 'pid=', '--ppid', str(watcher)], text=True, stdout=subprocess.PIPE, check=False).stdout.strip()
    if not children:
        command = Path(f'/proc/{watcher}/cmdline').read_bytes().split(b'\0')
        assert str(SWEEP / 'qualify_completed_modes.py').encode() in command
        os.kill(watcher, signal.SIGTERM)
        break
    time.sleep(5)

for mode in plan['modes']:
    capture = SWEEP / mode['capture_mode'] / 'capture'
    assert sha(capture / 'command.json') == mode['command_sha256']
    if not (capture / 'terminal.json').exists():
        command = load(capture / 'command.json')['argv']
        assert '--candidate-only' in command and '--native-reference-root' in command
        print('CAPTURING_OPENHCS_ONLY', mode['capture_mode'], flush=True)
        run(['python', str(capture / 'controller.py'), '--source-head', plan['source_revision']])
    terminal = load(capture / 'terminal.json')
    assert terminal['returncode'] == 0
    assert terminal['source_head_before'] == terminal['source_head_after'] == plan['source_revision']
    assert terminal['source_status_after'] == ''
    converted = capture / 'first_use_converted'
    if not (converted / 'summary_custody.json').exists():
        assert not converted.exists(), 'Partial conversion requires diagnosis; never silently overwrite'
        argv = harness_script(CONVERTER, '--suite-dir', str(capture), '--output-dir', str(converted))
        if mode['assignments'] > 1:
            argv.append('--scaling')
        run(argv)
    custody = load(converted / 'summary_custody.json')
    assert custody['status'] == 'PASS' and len(custody['cases']) == 30
    assert custody['converter_sha256'] == sha(CONVERTER)
    destination = RECORD / 'data/first_use' / mode['archive_mode']
    for name in ('first_use_execution_summary.csv', 'first_use_total_summary.csv', 'summary_custody.json'):
        preserve(converted / name, destination / name)
    run(harness_script(ARCHIVER, str(RECORD), str(SWEEP / 'official30-manifest.json'), str(CONVERTER), mode['archive_mode'], str(capture)), env={**os.environ, 'ARCHIVE_ROOT': str(RECORD)})
    preserve(capture / 'environment-source-seal.json', RECORD / 'protocol' / mode['archive_mode'] / 'environment-source-seal.json')
    print('FIRST_USE_ARCHIVED', mode['archive_mode'], flush=True)
print('REVISED_ALL_MODES_QUALIFIED', flush=True)
run(harness_script(RENDERER, '--record', str(RECORD), '--protocol-manifest', str(PLAN), '--output-dir', str(RECORD / 'figures')))
print('REVISED_FIGURES_RENDERED', flush=True)
(SWEEP / 'revised-sweep.terminal.json').write_text(json.dumps({'returncode': 0, 'qualified_modes': [m['archive_mode'] for m in plan['modes']], 'rendered_figures_root': str(RECORD / 'figures')}, indent=2) + '\n')
