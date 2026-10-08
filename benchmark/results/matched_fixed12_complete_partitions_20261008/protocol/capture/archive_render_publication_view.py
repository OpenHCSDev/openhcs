"""Archive a qualified post-terminal view and render only actual available modes.

No processing, CP execution, native model inference, or production-source/Git mutations.
The unchanged seven-mode verifier remains outside this scoped publication.
"""
from __future__ import annotations
import argparse
import csv
import hashlib
import json
import shutil
import sys
from dataclasses import replace
from pathlib import Path

HEAD = '753d4b26de7eab3ac592b29c10d70c2c769a6763'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--capture-root', type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument('--qualified-view', type=Path, required=True)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--result-root', type=Path, required=True, help='NEW benchmark/results record inside the owned results worktree')
    parser.add_argument('--figure-dir', type=Path, help='NEW scoped paper/figures/slas directory; required with --render')
    parser.add_argument('--comparison-root', type=Path, required=True)
    parser.add_argument('--render', action='store_true')
    args = parser.parse_args()
    args.capture_root = args.capture_root.resolve()
    load = lambda path: json.loads(path.read_text())
    def sha(path):
        with path.open('rb') as stream:
            return hashlib.file_digest(stream, 'sha256').hexdigest()
    def require(value, message):
        if not value:
            raise ValueError(message)
    for terminal in (args.capture_root / 'terminal.json', *(args.capture_root / f'receiving-{w}workers/terminal.json' for w in (1, 4))):
        require(terminal.is_file(), f'Capture not terminal: {terminal}')
        require(load(terminal) == {'returncode': 0, 'source_head': HEAD}, f'Terminal differs: {terminal}')
    require(not args.result_root.exists(), 'Fresh archive namespace required')
    if args.render:
        require(args.figure_dir is not None and not args.figure_dir.exists(), 'Fresh explicit figure directory required')
    names = {w: f'12assignments-{w}worker{"s" if w != 1 else ""}' for w in (1, 4)}
    custodies = {w: load(args.qualified_view / 'data/first_use' / name / 'summary_custody.json') for w, name in names.items()}
    goal = load(args.qualified_view / 'scaling_goal_summary.json')
    require(goal['source_head'] == HEAD and goal['workflow_count'] == 30 and goal['assignments'] == 12, 'Qualified goal scope differs')
    case_names = tuple(case['case'] for case in custodies[1]['cases'])
    require(len(case_names) == len(set(case_names)) == 30, 'Thirty distinct qualified cases required')
    inputs = {}
    for workers, custody in custodies.items():
        require(custody['status'] == 'PASS' and custody['source_head'] == HEAD, 'Qualified source/status differs')
        require(tuple(case['case'] for case in custody['cases']) == case_names, 'Matched case order differs')
        require(sha(args.source_root / 'benchmark/results/matched_worker_sweep_20261007_exportfixed/protocol/v2/convert_matched_reports.py') == custody['converter_sha256'], 'Original qualification owner differs')
        for key in ('manifest', 'capture_recipe', 'capture_terminal'):
            path = Path(custody[key]['path'])
            require(sha(path) == custody[key]['sha256'], f'Qualified {key} bytes changed')
            inputs[str(path)] = custody[key]['sha256']
        require(sha(Path(__file__).with_name('prepare_publication_view.py')) == custody['reporting_script_sha256'], 'Reporting derivation source differs')
        for case in custody['cases']:
            require(case['source_commit'] == HEAD and case['mode']['candidate_worker_count'] == workers and len(case['mode']['wells']) == 12, 'Qualified mode differs')
            require(tuple(row['repetition'] for row in case['rows']) == (0, 1, 2), 'Measured repetitions differ')
            for source, digest in case['raw_inputs'].items():
                require(sha(Path(source)) == digest, f'Original raw bytes changed: {source}')
                inputs[source] = digest
            anchor = case['native_headline_reference']
            require(anchor['kind'] == 'projected_first_batch' and anchor['target_native_observation_count'] == 0, 'CP projection label differs')
            require(sha(Path(anchor['source_report_path'])) == anchor['source_report_sha256'], 'Native anchor changed')
            inputs[anchor['source_report_path']] = anchor['source_report_sha256']
    comparison_path = args.comparison_root / 'comparison_custody.json'
    comparison = load(comparison_path)
    require(comparison['status'] == 'PASS' and comparison['source_head'] == HEAD
            and comparison['baseline_source_head'] == '7d13c202706f7582c4ec1f4a9874a441f67dad5f'
            and comparison['workflow_count'] == 30 and comparison['assignments'] == 12
            and comparison['workers'] == [1, 4], 'Whole-cohort comparison differs')
    for path_string, digest in comparison['input_sha256'].items():
        require(sha(Path(path_string)) == digest, f'Comparison input changed: {path_string}')
    for filename, digest in comparison['output_sha256'].items():
        require(sha(args.comparison_root / filename) == digest, f'Comparison output changed: {filename}')
    inputs[str(comparison_path)] = sha(comparison_path)
    reference_domains = {(case['native_execution_projection']['source_assignment_count'], case['native_execution_projection']['target_assignment_count']) for custody in custodies.values() for case in custody['cases']}
    require(len(reference_domains) == 1, 'Native source/target projection domains differ')
    native_source_count, native_target_count = reference_domains.pop()
    native_label = f'CP{native_target_count} projected from retained actual CP{native_source_count}'
    # File-copy contract follows existing archive_converted_modes.py: exact bytes,
    # no scientific TIFF/CSV/database duplication; retain relative custody layout.
    args.result_root.mkdir(parents=True)
    copies = {}
    def copy(source, destination):
        require(source.is_file(), f'Missing original: {source}')
        if destination.exists():
            require(sha(source) == sha(destination), f'Archive collision: {destination}')
        else:
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, destination)
        require(sha(source) == sha(destination), f'Copy mismatch: {destination}')
        copies[str(destination.relative_to(args.result_root))] = {'original_path': str(source), 'sha256': sha(destination)}
    for filename in ('all30_old_new_timings.csv', 'comparison_custody.json'):
        copy(args.comparison_root / filename, args.result_root / 'data' / 'comparison' / filename)
    for filename in ('actual_oh_fixed12_scaling.csv', 'scaling_goal_summary.json'):
        copy(args.qualified_view / filename, args.result_root / 'data' / filename)
    for filename in ('run.py', 'receive.py', 'source-and-environment.json', 'terminal.json', 'prepare_publication_view.py', 'archive_render_publication_view.py', 'compare_qualified_cohorts.py'):
        copy((Path(__file__).parent if filename in ('prepare_publication_view.py', 'archive_render_publication_view.py', 'compare_qualified_cohorts.py') else args.capture_root) / filename, args.result_root / 'protocol' / 'capture' / filename)
    for filename in ('convert_matched_reports.py', 'archive_converted_modes.py'):
        copy(args.source_root / 'benchmark/results/matched_worker_sweep_20261007_exportfixed/protocol/v2' / filename, args.result_root / 'protocol/v2' / filename)
    for workers, name in names.items():
        mode = args.qualified_view / 'data/first_use' / name
        custody = custodies[workers]
        for filename in ('first_use_execution_summary.csv', 'first_use_total_summary.csv', 'summary_custody.json'):
            copy(mode / filename, args.result_root / 'data' / name / filename)
        for filename in ('recipe.json', 'terminal.json'):
            copy(args.capture_root / f'receiving-{workers}workers' / filename, args.result_root / 'protocol' / name / filename)
        manifest = Path(custody['manifest']['path'])
        copy(manifest, args.result_root / 'protocol' / name / manifest.name)
        for case in custody['cases']:
            original = args.capture_root / f'receiving-{workers}workers/{workers}workers' / case['case']
            destination = args.result_root / 'reports' / name / case['case']
            native = load(original / 'native_report.json')
            native_origin = Path(native['request']['output_root']).parent
            for source_string in case['raw_inputs']:
                source = Path(source_string)
                require(source.suffix in ('.json', '.ready') or source.name == 'well_throughput_progress_events.csv', 'Only bounded original reporting records are archived')
                relative = source.relative_to(original) if source.is_relative_to(original) else Path('original_native') / source.relative_to(native_origin)
                copy(source, destination / relative)
            anchor = Path(case['native_headline_reference']['source_report_path'])
            copy(anchor, destination / 'original_native' / anchor.name)
            # Explicit derived declaration does not replace the original report.
            projection = destination / 'derived-native-reference.json'
            projection.write_text(json.dumps({'derivation': case['native_execution_projection'],
                'original_report': case['native_headline_reference'], 'raw_case_report_sha256': sha(original / 'report.json')}, indent=2) + '\n')
            copies[str(projection.relative_to(args.result_root))] = {'derived': True, 'sha256': sha(projection)}
    policy = {
        'source_head': HEAD, 'scope': '30 official workflows, fixed12 independent repeated assignments, actual1/4 workers',
        'actual_measurements': 'Warmup -1 preserved; medians use actual0/1/2; full SERVER_PIPELINE_JOB execution',
        'total_scope': 'Original additive compile/execute SUBMIT+WAIT total; separate server compile+execute rows retained in custody',
        'goal': goal, 'native_reference': native_label + ' fresh+warm via existing RepeatedSourceNativeBatchReport; target native observations0',
        'historical_record': 'Original seven-mode publication/verifier unchanged; no invented2/3-worker modes or new singlewell capture',
        'publication_status': 'Qualified record; root reviews rendered artifacts before the already authorized commit and publication',
    }
    (args.result_root / 'README.md').write_text('# Matched fixed12 one/four-worker capture\n\n' + '\n\n'.join(f'{key}: {value}' for key, value in policy.items() if key != 'goal') + '\n')
    receipt = {'status': 'PASS', 'source_head': HEAD, 'original_input_sha256': inputs, 'archive_files': copies,
               'reporting_owner_sha256': sha(Path(__file__)), 'policy': policy, 'rendered': False}
    if args.render:
        sys.path.insert(0, str(args.source_root))
        sys.path.insert(0, str(args.source_root / 'paper/figures'))
        from benchmark.reports import cppipe_figures as figures
        import build_slas_agent
        normalize_generated_svg = build_slas_agent.normalize_generated_svg
        args.figure_dir.mkdir(parents=True)
        generated = []
        for scope in ('execution', 'total'):
            actual, projected = [], []
            tables = {}
            for workers, name in names.items():
                summary = args.result_root / 'data' / name / f'first_use_{scope}_summary.csv'
                with summary.open(newline='') as stream:
                    table = {row['case_name']: row for row in csv.DictReader(stream)}
                require(tuple(table) == case_names, 'Archived summary case order differs')
                tables[workers] = table
                source = figures.SummarySource(f'OH {workers} worker{"s" if workers != 1 else ""} / 12 assignments', summary)
                for name in case_names:
                    cp, oh = source.metric_rows(name, table[name], category_row=table[name])
                    if workers == 1:
                        projected.append(replace(cp, method=native_label))
                    projected.append(oh)
                    ratio = float(tables[1][name]['median_openhcs_execution_seconds']) / oh.raw_seconds
                    actual.append(replace(oh, speedup=ratio))
            actual_dir = args.figure_dir / 'actual_oh' / scope
            reference_dir = args.figure_dir / 'projected_cp_reference' / scope
            actual_dir.mkdir(parents=True); reference_dir.mkdir(parents=True)
            for directory, rows in ((actual_dir, actual), (reference_dir, projected)):
                metrics = directory / 'workflow_metrics.csv'
                figures._write_metric_rows(metrics, rows)
                generated.append(metrics)
            generated.extend(figures.generate_grouped_benchmark_metric_figures(actual,
                metrics=(figures.FigureMetricSpec('raw_seconds', 'actual_oh_runtime', f'Fixed12 actual OH {scope} warmed medians', 'Seconds', log_variant=True),
                         figures.FigureMetricSpec('speedup', 'actual_oh_scaling', f'Fixed12 actual OH {scope} one/four scaling', 'OH1 / OHn', target_line=goal['target'], log_variant=True)),
                methods=tuple(dict.fromkeys(row.method for row in actual)), pipeline_names=case_names,
                output_dir=actual_dir, output_formats=('png', 'svg')))
            generated.extend(figures.FIGURE_STYLE.generate_average_point_figures(actual,
                methods=tuple(dict.fromkeys(row.method for row in actual)), output_dir=actual_dir, output_formats=('png', 'svg'),
                filename_stem='actual_oh_scaling_distribution', title=f'12 measured assignments · 30 workflows · {scope}',
                ylabel='Actual OH one-worker / n-worker speedup', value_key='speedup', target_line=goal['target'], log_variant=True, annotation_precision=3))
            generated.extend(figures.generate_grouped_benchmark_metric_figures(projected,
                metrics=(figures.FigureMetricSpec('raw_seconds', 'projected_cp_runtime', f'{native_label} / actual OH {scope}', 'Seconds', log_variant=True),
                         figures.FigureMetricSpec('speedup', 'projected_cp_ratio', f'{native_label} / actual OH {scope}', f'CP{native_target_count} projected / OH', target_line=figures.SPEEDUP_TARGET, log_variant=True)),
                methods=tuple(dict.fromkeys(row.method for row in projected)), pipeline_names=case_names,
                output_dir=reference_dir, output_formats=('png', 'svg')))
            oh_rows = tuple(row for row in projected if row.method.startswith('OH '))
            generated.extend(figures.FIGURE_STYLE.generate_average_point_figures(oh_rows,
                methods=tuple(dict.fromkeys(row.method for row in oh_rows)), output_dir=reference_dir, output_formats=('png', 'svg'),
                filename_stem='projected_cp_ratio_distribution', title=f'{native_label} · OH {scope} medians',
                ylabel=f'CP{native_target_count} projected reference / OH', value_key='speedup', target_line=figures.SPEEDUP_TARGET, log_variant=True))
        caption = args.figure_dir / 'caption.md'
        caption.write_text('Actual OH panels use same-head fixed12 full-output-complete warmed medians, three measured observations per workflow and mode. Full server execution includes saving, publication and finalization; total uses the original disjoint compile/execute client phases. Workflow dots, arithmetic mean bars and median lines use the existing May figure owner. OH scaling target is ' + str(goal['target']) + f'×. Measured median execution scaling is {goal["median_scaling_by_scope"]["execution"]:.9f}× and total scaling is {goal["median_scaling_by_scope"]["total"]:.9f}×; the execution target is {"reached" if goal["execution_target_met"] else "not reached"}. Separate CP-reference panels use {native_label}; no CP{native_target_count} execution was observed. Their 2× reference guide is independent of the OH scaling target. Warm observations and all input/receipt/progress/hash custody are retained. No RAM values, unobserved workers 2/3, or fresh singlewell claims are supplied.\n')
        generated.append(caption)
        for path in generated:
            if path.suffix == '.svg': normalize_generated_svg(path)
        figure_receipt = {'source_head': HEAD, 'policy': policy,
            'archive_custody_sha256': {str(path.relative_to(args.result_root)): sha(path) for path in args.result_root.rglob('summary_custody.json')},
            'owner_sha256': {str(Path(owner.__file__)): sha(Path(owner.__file__)) for owner in (figures, build_slas_agent)},
            'output_sha256': {str(path.relative_to(args.figure_dir)): sha(path) for path in generated},
            'rendering_script_sha256': sha(Path(__file__)), 'visual_review': 'PENDING'}
        (args.figure_dir / 'figure_provenance.json').write_text(json.dumps(figure_receipt, indent=2) + '\n')
        receipt['rendered'] = True
        receipt['figure_provenance'] = str(args.figure_dir / 'figure_provenance.json')
    (args.result_root / 'archive_custody.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'archived': str(args.result_root), 'rendered': args.render, 'visual_review': 'PENDING'}))


if __name__ == '__main__':
    main()
