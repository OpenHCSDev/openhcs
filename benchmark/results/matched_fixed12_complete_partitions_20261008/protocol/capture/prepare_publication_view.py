"""Post-terminal reporting only: unchanged captures, existing qualification owners.

Prepared scaffold; never run during capture. Does not render or launch processing.
"""
from __future__ import annotations
import argparse
import csv
import importlib.util
import json
import statistics
import subprocess
import sys
from pathlib import Path

HEAD = '753d4b26de7eab3ac592b29c10d70c2c769a6763'
CONVERTER = Path('benchmark/results/matched_worker_sweep_20261007_exportfixed/protocol/v2/convert_matched_reports.py')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--capture-root', type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--scaling-target', type=float, default=3.0)
    args = parser.parse_args()
    # Check all terminal receipts BEFORE importing owners or reading case reports.
    load = lambda p: json.loads(p.read_text())
    for terminal in (args.capture_root / 'terminal.json', *(args.capture_root / f'receiving-{w}workers/terminal.json' for w in (1, 4))):
        if not terminal.is_file():
            raise SystemExit(f'NOT READY: missing terminal receipt {terminal}')
        if load(terminal) != {'returncode': 0, 'source_head': HEAD}:
            raise SystemExit(f'NOT READY: terminal does not admit this source {terminal}')
    if args.output_dir.exists():
        raise SystemExit('Fresh derived output namespace required')
    if subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=args.source_root, text=True).strip() != HEAD:
        raise SystemExit('Exact captured source is required for the reporting owners')
    sys.path.insert(0, str(args.source_root))
    module_spec = importlib.util.spec_from_file_location('original_matched_converter', args.source_root / CONVERTER)
    owner = importlib.util.module_from_spec(module_spec)
    sys.modules[module_spec.name] = owner
    module_spec.loader.exec_module(owner)
    from benchmark.native_execution_projection import RepeatedSourceNativeBatchReport

    sha, require = owner.sha, owner.require
    recipes = {w: load(args.capture_root / f'receiving-{w}workers/recipe.json') for w in (1, 4)}
    declaration = {'argv': recipes[1]['common_argv']}
    manifest = Path(owner.argument(declaration, '--manifest'))
    cases = tuple(c['name'] for c in load(manifest)['cases'])
    require(len(cases) == len(set(cases)) == 30, 'Expected exactly official thirty workflows')
    require(all(tuple(r['cases']) == cases and r['source'] == HEAD for r in recipes.values()), 'Recipe/source/ordered cohort differs')
    require(all('--native-execution-model' not in r['common_argv'] for r in recipes.values()), 'This scaffold admits only unchanged model-pending captures')
    derived = {}
    for workers, recipe in recipes.items():
        command = {'argv': recipe['common_argv']}
        require(owner.argument(command, '--repeat-assignments') == '12' and owner.argument(command, '--repetitions') == '3', 'Actual captured workload differs')
        metadata, summary_rows = [], {'execution': [], 'total': []}
        for name in cases:
            case = args.capture_root / f'receiving-{workers}workers/{workers}workers' / name
            paths = {key: case / filename for key, filename in (
                ('provenance', 'pilot_provenance.json'), ('native', 'native_report.json'),
                ('candidate', 'candidate_report.json'), ('report', 'report.json'), ('request', 'native_request.json'))}
            p, native, observations, report = (load(paths[key]) for key in ('provenance', 'native', 'candidate', 'report'))
            require(p['case'] == name and p['source_commit'] == HEAD and p['source_dirty'] is False, 'Production source differs')
            require(p['manifest_sha256'] == sha(manifest), 'Manifest differs')
            require(p['native_input_inventory'] and p['native_input_inventory'] == p['native_input_inventory_after'], 'Input custody differs')
            require(p['candidate_worker_count'] == workers and len(set(p['wells'])) == len(p['wells']) == 12, 'Candidate domain differs')
            require(p['native_job_count'] == 1 and p['native_capture_status'] == 'retained_projection_source', 'Native source role differs')
            require(report['native'] == native and report['candidate'] == observations, 'Raw report payload differs')
            require(native['request'] == load(paths['request']), 'Native request differs')
            view = RepeatedSourceNativeBatchReport.from_payload(native)
            view.require_complete(3)
            require(len(view.assignment_directories) == 8, 'Expected genuine retained8 native anchor')
            source = Path(p['native_reference_report_path'])
            require(sha(source) == p['native_reference_report_sha256'] and load(source) == native, 'Native anchor custody differs')
            inputs = view.projection_inputs(12, source_report_path=source, source_report_sha256=sha(source))
            require(report['native_execution_projection'] == json.loads(json.dumps(inputs)), 'Original model-pending inputs differ')
            projection = view.projected_fresh_batch(12, source_report_path=source, source_report_sha256=sha(source))
            require(tuple(o['repetition'] for o in observations) == (-1, 0, 1, 2), 'All four actual observations required')
            native_rows = {o['repetition']: o for o in native['observations']}
            rows, receipts, environments = [], [], []
            raw = {str(path): sha(path) for path in paths.values()}
            for observed in observations:
                phases, total, receipt, hashes = owner.qualify_candidate(
                    observed, p, native_rows[observed['repetition']], view.assignment_directories,
                    view.comparison_directories(12), scaling=True, projected=True)
                raw.update(hashes)
                receipts.append({'path': observed['receipt_path'], 'sha256': hashes[observed['receipt_path']], 'execution_id': observed['execution_id'], 'repetition': observed['repetition']})
                environments.append(receipt['server_environment'])
                if observed['repetition'] >= 0:
                    rows.append({'repetition': observed['repetition'], 'openhcs_execution_seconds': phases['SERVER_PIPELINE_JOB'],
                                 'openhcs_total_seconds': total, 'openhcs_compile_seconds': phases['SERVER_COMPILATION_JOB'],
                                 'openhcs_server_compile_plus_execution_seconds': phases['SERVER_COMPILATION_JOB'] + phases['SERVER_PIPELINE_JOB'],
                                 'native_execution_seconds': projection['projected_fresh_batch_execution_seconds'],
                                 'native_total_seconds': projection['projected_fresh_batch_prepared_invocation_seconds']})
            require(all(e == environments[0] for e in environments), 'Mixed observation environment')
            headline = {'kind': 'projected_first_batch', 'execution_seconds': projection['projected_fresh_batch_execution_seconds'],
                        'prepared_invocation_seconds': projection['projected_fresh_batch_prepared_invocation_seconds'],
                        'source_report_path': str(source), 'source_report_sha256': sha(source),
                        'source_fresh_repetition': -1, 'source_fresh_observation_count': 1, 'target_native_observation_count': 0}
            item = {'case': name, 'source_commit': HEAD, 'rows': rows, 'receipts': receipts, 'raw_inputs': raw,
                    'server_environment': environments[0], 'native_environment': native['environment'],
                    'thread_environment': p['thread_environment'], 'native_headline_reference': headline,
                    'native_execution_projection': projection, 'native_observations': native['observations'],
                    'input_inventory': p['native_input_inventory'],
                    'mode': {key: p[key] for key in ('wells', 'selected_source_wells', 'assignment_scope', 'native_job_count', 'candidate_worker_count', 'candidate_worker_start_method')}}
            metadata.append(item)
            for scope in summary_rows:
                oh = statistics.median(row[f'openhcs_{scope}_seconds'] for row in rows)
                cp = headline['execution_seconds' if scope == 'execution' else 'prepared_invocation_seconds']
                summary_rows[scope].append({'case_name': name, 'assay_category': '', 'module_category': '', 'n': 3, 'equivalent_count': 3,
                    'native_observation_count': 0, 'native_reference_kind': headline['kind'],
                    'median_native_execution_seconds': cp, 'median_openhcs_execution_seconds': oh,
                    'median_speedup': cp / oh, 'median_native_peak_memory_mb': '', 'median_openhcs_peak_memory_mb': '',
                    'min_parity_accuracy': 1.0, 'speedup_target': owner.SPEEDUP_TARGET})
        require(all(m['server_environment'] == metadata[0]['server_environment'] and m['thread_environment'] == metadata[0]['thread_environment'] for m in metadata), 'Mixed case server/thread environment')
        require(all({k: v for k, v in m['native_environment'].items() if k != 'temporary_root'} == {k: v for k, v in metadata[0]['native_environment'].items() if k != 'temporary_root'} for m in metadata), 'Mixed native environment')
        derived[workers] = (metadata, summary_rows)
    for left, right in zip(derived[1][0], derived[4][0], strict=True):
        # Both captures already admitted their unchanged inputs against this
        # exact retained anchor through the captured source/reuse authority.
        # Temporary staging paths remain provenance, not a second match policy.
        require(left['case'] == right['case'] and left['native_headline_reference'] == right['native_headline_reference'], 'Matched admitted source anchor differs')
        require(all(left['mode'][key] == right['mode'][key] for key in ('wells', 'selected_source_wells', 'assignment_scope')), 'Matched workload differs')
    # Writes happen only after the whole two-mode matrix qualified successfully.
    args.output_dir.mkdir(parents=True)
    def write_csv(path, rows):
        with path.open('w', newline='') as stream:
            writer = csv.DictWriter(stream, fieldnames=tuple(rows[0])); writer.writeheader(); writer.writerows(rows)
    for workers, (metadata, summaries) in derived.items():
        mode = args.output_dir / 'data' / 'first_use' / f'12assignments-{workers}worker{"s" if workers != 1 else ""}'
        mode.mkdir(parents=True)
        for scope, rows in summaries.items(): write_csv(mode / f'first_use_{scope}_summary.csv', rows)
        custody = {'status': 'PASS', 'source_head': HEAD, 'cases': metadata,
            'manifest': {'path': str(manifest), 'sha256': sha(manifest)}, 'converter_sha256': sha(args.source_root / CONVERTER),
            'derivation': 'Post-terminal reporting view, not original capture declaration. Existing converter.qualify_candidate owns measurement/SCI admission; existing native projection owner supplies separately authorized CP12 reference.',
            'capture_recipe': {'path': str(args.capture_root / f'receiving-{workers}workers/recipe.json'), 'sha256': sha(args.capture_root / f'receiving-{workers}workers/recipe.json')},
            'capture_terminal': {'path': str(args.capture_root / f'receiving-{workers}workers/terminal.json'), 'sha256': sha(args.capture_root / f'receiving-{workers}workers/terminal.json')},
            'reporting_script_sha256': sha(Path(__file__)), 'goal_scope': 'Actual warmed OH fixed12 one/four full-job medians; CP projection is separate reference only'}
        (mode / 'summary_custody.json').write_text(json.dumps(custody, indent=2) + '\n')
    scaling = []
    for scope in ('execution', 'total'):
        for one, four in zip(derived[1][1][scope], derived[4][1][scope], strict=True):
            a, b = one['median_openhcs_execution_seconds'], four['median_openhcs_execution_seconds']
            scaling.append({'case_name': one['case_name'], 'scope': scope, 'assignments': 12, 'one_worker_median_seconds': a,
                'four_worker_median_seconds': b, 'actual_one_over_four_scaling': a / b, 'target': args.scaling_target,
                'meets_target': a / b >= args.scaling_target, 'source_head': HEAD})
    write_csv(args.output_dir / 'actual_oh_fixed12_scaling.csv', scaling)
    aggregate = {
        scope: statistics.median(row['actual_one_over_four_scaling'] for row in scaling if row['scope'] == scope)
        for scope in ('execution', 'total')
    }
    (args.output_dir / 'scaling_goal_summary.json').write_text(json.dumps({
        'source_head': HEAD, 'workflow_count': len(cases), 'assignments': 12,
        'target': args.scaling_target, 'median_scaling_by_scope': aggregate,
        'execution_target_met': aggregate['execution'] >= args.scaling_target,
        'completion_scope': 'Measured scaling gate only; publication and merged artifacts remain separately required.',
    }, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'cases': len(cases), 'modes': (1, 4), 'output_dir': str(args.output_dir), 'rendered': False}))


if __name__ == '__main__':
    main()
