"""Capture one supplied production freeze; reuse qualified native anchors."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--plan', type=Path, required=True)
parser.add_argument('--prepare-only', action='store_true', help='Seal commands only after the supplied production freeze is known')
options = parser.parse_args()
PLAN = options.plan.resolve()
plan = json.loads(PLAN.read_text())
assert plan['status'] == 'PREPARED_REVISED_CAPTURE_PROTOCOL', 'Production freeze is not admitted'
assert isinstance(plan['source_revision'], str) and len(plan['source_revision']) == 40
SWEEP = Path(plan['capture_root'])
WORKTREE = Path(plan['artifact_worktree'])
PRODUCTION = Path(plan['production_worktree'])
RECORD = WORKTREE / 'benchmark/results' / plan['record_name']
PYTHON = plan['python_executable']
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
        f'sys.path.insert(0,{str(PRODUCTION)!r});'
        'import benchmark,runpy;'
        f'benchmark.__path__={[str(WORKTREE / "benchmark")]!r};'
        'sys.argv=sys.argv[1:];runpy.run_path(sys.argv[0],run_name="__main__")'
    )
    return ['taskset', '-c', '0', PYTHON, '-B', '-c', bootstrap, str(script), *arguments]

def capture_argv(mode):
    """Derive common harness/cache bindings once, preserving authored mode scope."""
    argv = list(mode['command_template_argv'])
    python_index = argv.index(PYTHON)
    bootstrap_index = argv.index('-c', python_index + 1) + 1
    argv[bootstrap_index] = (
        f'import sys;sys.path.insert(0,{str(PRODUCTION)!r});'
        f'import benchmark;benchmark.__path__={[str(WORKTREE / "benchmark")]!r};'
        + plan['capture_bootstrap_body']
    )
    for flag, value in (
        ('--production-source-root', PRODUCTION),
        ('--native-measurement-cache-root', plan['native_facts_cache_root']),
    ):
        if flag in argv:
            argv[argv.index(flag) + 1] = str(value)
        else:
            argv.extend((flag, str(value)))
    return argv

def run(argv, **kwargs):
    subprocess.run(argv, cwd=WORKTREE, check=True, **kwargs)

assert plan['status'] == 'PREPARED_REVISED_CAPTURE_PROTOCOL'
assert sha(CONVERTER) == plan['converter_sha256']
assert sha(ARCHIVER) == plan['archive_owner_sha256']
assert sha(RENDERER) == plan['render_owner_sha256']

if options.prepare_only:
    for mode in plan['modes']:
        capture = SWEEP / mode['capture_mode'] / 'capture'
        assert not (capture / 'suite.log').exists(), 'Never prepare over an existing capture'
        capture.mkdir(parents=True, exist_ok=True)
        command = {'status': 'PREPARED_FINAL_COHORT_NOT_LAUNCHED',
                   'source_freeze_head': plan['source_revision'],
                   'argv': capture_argv(mode)}
        command_path = capture / 'command.json'
        content = json.dumps(command, indent=2) + '\n'
        if command_path.exists():
            assert command_path.read_text() == content, 'Never replace a different prepared command'
        else:
            command_path.write_text(content)
        preserve(RECORD / 'protocol/v2/controller-template.py', capture / 'controller.py')
        mode['command_path'] = str(command_path)
        mode['command_sha256'] = sha(command_path)
    PLAN.write_text(json.dumps(plan, indent=2) + '\n')
    print('FROZEN_COMMANDS_PREPARED_NO_CAPTURE_LAUNCHED', flush=True)
    sys.exit(0)

for mode in plan['modes']:
    capture = SWEEP / mode['capture_mode'] / 'capture'
    assert sha(capture / 'command.json') == mode['command_sha256']
    command = load(capture / 'command.json')['argv']
    if not (capture / 'terminal.json').exists():
        assert '--native-reference-root' in command
        assert ('--candidate-only' in command) == (mode['target_native_observation_count'] == 0)
        print('CAPTURING_OPENHCS_ONLY', mode['capture_mode'], flush=True)
        run([PYTHON, str(capture / 'controller.py'), '--source-head', plan['source_revision'], '--source-root', str(PRODUCTION)])
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
    run(harness_script(ARCHIVER, str(RECORD), command[command.index('--manifest') + 1], str(CONVERTER), mode['archive_mode'], str(capture)), env={**os.environ, 'ARCHIVE_ROOT': str(RECORD)})
    preserve(capture / 'environment-source-seal.json', RECORD / 'protocol' / mode['archive_mode'] / 'environment-source-seal.json')
    print('FIRST_USE_ARCHIVED', mode['archive_mode'], flush=True)
print('REVISED_ALL_MODES_QUALIFIED', flush=True)
run(harness_script(RENDERER, '--record', str(RECORD), '--protocol-manifest', str(PLAN), '--output-dir', str(RECORD / 'figures')))
print('REVISED_FIGURES_RENDERED', flush=True)
(SWEEP / 'revised-sweep.terminal.json').write_text(json.dumps({'returncode': 0, 'qualified_modes': [m['archive_mode'] for m in plan['modes']], 'rendered_figures_root': str(RECORD / 'figures')}, indent=2) + '\n')
