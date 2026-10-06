"""Derive existing SummarySource CSV inputs from qualified matched reports.
Default: full-manifest singlewell headline. Explicit --scaling: actual repeated
assignments with one or concurrent native/OH workers, never projected native timings.
No execution, projection or figure generation. Reads the existing suite terminal.
"""
import argparse
import csv
import hashlib
import json
import math
import statistics
from collections import Counter
from dataclasses import replace
from pathlib import Path
from benchmark.native_batch_contracts import NativeBatchReport, NativeBatchRequest
from benchmark.native_synthetic_well_scaling import _concurrent_timing
from benchmark.matched_cellprofiler_batch import _worker_axis_evidence
from benchmark.timing import PhaseTimingRecord, additive_phase_total_seconds
from benchmark.reports.cppipe_figures import SPEEDUP_TARGET
from openhcs.core.progress.types import ProgressEvent
from openhcs.core.source_projection import OpenHCSPlaneAddress

def load(path):
    return json.loads(path.read_text())

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(condition, message):
    if not condition:
        raise ValueError(message)

def median(values):
    require(all(math.isfinite(v) and v > 0 for v in values), 'Invalid measured duration')
    return statistics.median(values)

def scaling_native_rows(case_dir, provenance, repetitions, command, native):
    """Qualify actual assignment/shard owners; never project serial durations."""
    argv = command['argv']
    require(repetitions == int(argv[argv.index('--repetitions') + 1]) == 3, 'Scaling figures require three command-declared measured repetitions')
    require(provenance['manifest_sha256'] == sha(Path(argv[argv.index('--manifest') + 1])), 'Scaling command manifest differs from prepared report')
    if '--case' in argv:
        require(provenance['case'] == argv[argv.index('--case') + 1], 'Scaling case differs from command')
    assignments = int(argv[argv.index('--repeat-assignments') + 1])
    workers = int(argv[argv.index('--openhcs-workers') + 1])
    jobs = int(argv[argv.index('--native-jobs') + 1])
    wells = tuple(provenance['wells'])
    require(assignments == len(wells) and len(set(wells)) == assignments, 'Assignment count differs from command')
    require(workers == jobs == provenance['candidate_worker_count'] == provenance['native_job_count'], 'Actual native/OH worker counts differ')
    require(jobs >= 1 and assignments >= jobs and assignments % jobs == 0, 'Scaling requires actual evenly partitioned workers')
    require(provenance['assignment_scope'] == 'independent repeated source assignments' and len(provenance['selected_source_wells']) == 1, 'Scaling requires one selected source well and explicit repeated assignments')
    serial = NativeBatchReport.from_payload(native)
    require(serial.request == NativeBatchRequest(**load(case_dir / 'native_request.json')), 'Serial request/report differ')
    directories = tuple(OpenHCSPlaneAddress.component_token(well) for well in wells)
    require(serial.request.assignment_output_subdirectories == directories, 'Serial assignment roles differ from declared wells')
    require(serial.request.first_image_set == 1 and serial.request.last_image_set is None and serial.request.start_barrier_root is None, 'Serial baseline has a different image-set/barrier scope')
    serial.require_complete(repetitions)
    serial_domains = tuple(tuple((directory, count) for directory, count in row.assignment_image_set_counts) for row in serial.observations)
    require(len(set(serial_domains)) == 1 and len({count for _, count in serial_domains[0]}) == 1, 'Serial assignments do not execute equal independent source domains')
    require(all(row.image_set_count == provenance['native_image_set_count'] for row in serial.observations), 'Serial image-set count differs from provenance')
    require(all(tuple(directory for directory, _ in domain) == directories for domain in serial_domains), 'Serial observations do not cover exact assignment roles')
    if jobs == 1:
        require(not (case_dir / 'native_shards' / 'reports.json').exists(), 'Serial mode must not borrow native shard timings')
        return None, {str(case_dir / 'native_request.json'): sha(case_dir / 'native_request.json')}, ()
    shards_path = case_dir / 'native_shards' / 'reports.json'
    equivalence_path = case_dir / 'native_shards' / 'equivalence.json'
    shards = tuple(load(shards_path))
    require(len(shards) == jobs, 'Incomplete native job reports')
    partition = assignments // jobs
    image_sets = provenance['native_image_set_count'] // jobs
    require(provenance['native_image_set_count'] % jobs == 0, 'Native image sets do not partition evenly')
    for index, payload in enumerate(shards):
        report = NativeBatchReport.from_payload(payload)
        report.require_complete(repetitions)
        request = NativeBatchRequest(**load(case_dir / 'native_shards' / f'request_{index}.json'))
        require(report.request == request, 'Native shard request/report differ')
        expected = replace(
            serial.request,
            output_root=str(case_dir / 'native_shards' / str(index)),
            expected_image_sets=image_sets,
            assignment_output_subdirectories=directories[index * partition:(index + 1) * partition],
            start_barrier_root=str(case_dir / 'native_shards' / 'start_barrier'),
            start_barrier_job_count=jobs,
            start_barrier_job_index=index,
            report_path=str(case_dir / 'native_shards' / f'{index}_report.json'),
        )
        require(request == expected, 'Native shard does not own its exact serial workload partition/barrier')
        require(load(Path(request.report_path)) == payload, 'Original native worker report differs from shard collection')
        serial.environment.require_equivalent(report.environment)
        expected_domain = serial_domains[0][index * partition:(index + 1) * partition]
        require(all(tuple((directory, count) for directory, count in row.assignment_image_set_counts) == expected_domain and row.image_set_count == image_sets for row in report.observations), 'Native shard assignment coverage differs')
    equivalence = tuple(load(equivalence_path))
    require(tuple(row['repetition'] for row in equivalence) == tuple(range(-1, repetitions)), 'Incomplete/reordered native shard science')
    timing_rows = {}
    for row in equivalence:
        require(row['differences'] == [], 'Native shard science differs from serial baseline')
        actual = _concurrent_timing(shards, row['repetition'])
        require(all(math.isclose(row[key], value, rel_tol=0.0, abs_tol=1e-9) for key, value in actual.items()), 'Native reported makespan disagrees with original simultaneous clocks')
        timing_rows[row['repetition']] = row
    return timing_rows, {str(path): sha(path) for path in (case_dir / 'native_request.json', shards_path, equivalence_path, *(case_dir / 'native_shards' / f'{index}_report.json' for index in range(jobs)), *(case_dir / 'native_shards' / f'request_{index}.json' for index in range(jobs)))}, shards

def convert(case_dir, source_commit, repetitions, *, scaling=False, command=None):
    provenance_path = case_dir / 'pilot_provenance.json'
    native_path = case_dir / 'native_report.json'
    candidate_path = case_dir / 'candidate_report.json'
    provenance = load(provenance_path)
    require(provenance['source_commit'] == source_commit and provenance['source_dirty'] is False, f'{case_dir}: source mismatch/dirty')
    if not scaling:
        require(len(provenance['wells']) == provenance['candidate_worker_count'] == provenance['native_job_count'] == 1, 'Headline requires measured 1w1t native and OH')
    else:
        require(command is not None and '--repeat-assignments' in command['argv'], 'Scaling must derive from an explicit repeated-assignment command')
        require(command['source_freeze_head'] == source_commit, 'Scaling command source differs')
    require(provenance['native_input_inventory'] and provenance['native_input_inventory'] == provenance['native_input_inventory_after'], 'Input custody mismatch')
    native = load(native_path)
    NativeBatchReport.from_payload(native).require_complete(repetitions)
    shard_inputs, shard_reports = {}, ()
    concurrent = None
    if scaling:
        concurrent, shard_inputs, shard_reports = scaling_native_rows(case_dir, provenance, repetitions, command, native)
    native_rows = {row['repetition']: row for row in native['observations'] if row['repetition'] >= 0}
    candidate = load(candidate_path)
    if scaling:
        require(tuple(row['repetition'] for row in candidate) == tuple(range(-1, repetitions)), 'Incomplete/reordered actual candidate observations')
        for c in candidate:
            require(c['declared_output_file_count'] is not None and c['declared_output_file_count'] > 0 and c['native_output_file_count'] > 0, 'Vacuous scaling warmup/measured output comparison')
            require(c['native_image_count'] == c['candidate_image_count'] and c['native_physical_image_count'] == c['candidate_physical_image_count'], 'Scaling warmup/measured image inventory differs')
            require(len(c['native_output_inventory']) == c['native_output_file_count'] and len(c['candidate_output_inventory']) == c['candidate_output_file_count'], 'Scaling warmup/measured output inventories incomplete')
            require(all(item['sha256'] for key in ('native_output_inventory', 'candidate_output_inventory') for item in c[key]), 'Scaling warmup/measured output hashes absent')
            require(c['assignment_scope'] == provenance['assignment_scope'] and tuple(c['compared_assignments']) == tuple(provenance['wells']), 'Candidate science does not cover exact assignments')
            receipt = load(Path(c['receipt_path']))
            require(receipt['execution_id'] == c['execution_id'] and receipt['compile_artifact_id'] == c['compile_artifact_id'], 'Scaling progress receipt identity differs')
            require(c['observation_scope'] == receipt['observation_export_scope'] == 'outcomes', 'Scaling must retain ordinary OUTCOMES, not VALUES capture')
            progress_path = Path(c['receipt_path']).parent / 'well_throughput_progress_events.csv'
            with progress_path.open(newline='') as handle:
                progress = tuple(csv.DictReader(handle))
            require(all(row['case_name'] == provenance['case'] and int(row['worker_count']) == provenance['candidate_worker_count'] and int(row['well_count']) == len(provenance['wells']) for row in progress), 'Saved worker progress mode differs')
            events = tuple(ProgressEvent.from_dict({**row, 'execution_id': c['execution_id'], 'plate_id': receipt['execution_plate_id'], 'timestamp': float(row['timestamp']), 'pid': int(row['pid']), 'percent': float(row['percent']), 'completed': int(row['completed']), 'total': int(row['total'])}) for row in progress if row['phase'] in ('axis_started', 'axis_completed'))
            evidence = _worker_axis_evidence(events, execution_id=c['execution_id'], expected_axes=len(provenance['wells']), expected_workers=provenance['candidate_worker_count'])
            require(tuple(evidence['worker_process_ids']) == tuple(c['worker_process_ids']) and math.isclose(evidence['worker_interval_overlap_seconds'], c['worker_interval_overlap_seconds'], rel_tol=0.0, abs_tol=1e-9), 'Candidate worker concurrency differs from saved progress')
            require({event['axis_id'] for event in c['axis_events']} == set(provenance['wells']), 'Candidate axes do not match requested assignment identities')
            require({(event.axis_id, event.phase.value, event.timestamp, event.pid) for event in events} == {(event['axis_id'], event['phase'], event['timestamp'], event['pid']) for event in c['axis_events']}, 'Candidate axis report differs from original progress')
            require(all(c[key] == [] for key in ('database_differences', 'csv_differences', 'image_differences', 'unexpected_output_files', 'missing_declared_output_files')), 'Candidate assignment science failed')
            require(receipt['expected_axis_count'] == receipt['observed_axis_count'] == c['axis_count'] == len(provenance['wells']), 'Scaling receipt axis domain differs')
            shard_inputs[str(progress_path)] = sha(progress_path)
    candidate_rows = {row['repetition']: row for row in candidate if row['repetition'] >= 0}
    require(set(native_rows) == set(candidate_rows) == set(range(repetitions)), 'Incomplete measured repetitions')
    rows, receipts, environments = [], [], []
    for rep in range(repetitions):
        n, c = native_rows[rep], candidate_rows[rep]
        axes = len(provenance['wells'])
        require(c['axis_count'] == axes and n['image_set_count'] == provenance['native_image_set_count'] > 0, 'Wrong acquired/axis domain')
        for key in ('database_differences', 'csv_differences', 'image_differences', 'unexpected_output_files', 'missing_declared_output_files'):
            require(c[key] == [], f'{case_dir} rep{rep}: {key}')
        require(c['declared_output_file_count'] is not None and c['declared_output_file_count'] > 0 and c['native_output_file_count'] > 0, 'Vacuous output comparison')
        require(c['native_image_count'] == c['candidate_image_count'] and c['native_physical_image_count'] == c['candidate_physical_image_count'], 'Image inventory mismatch')
        require(len(c['native_output_inventory']) == c['native_output_file_count'] and len(c['candidate_output_inventory']) == c['candidate_output_file_count'], 'Incomplete output inventories')
        require(all(item['sha256'] for key in ('native_output_inventory','candidate_output_inventory') for item in c[key]), 'Missing output hashes')
        receipt_path = Path(c['receipt_path'])
        receipt = load(receipt_path)
        require(receipt['execution_id'] == c['execution_id'] and receipt['compile_artifact_id'] == c['compile_artifact_id'], 'Receipt identity mismatch')
        require(receipt['pipeline_name'] == provenance['case'], 'Recipe identity mismatch')
        require(receipt['expected_axis_count'] == receipt['observed_axis_count'] == axes, 'Receipt axis mismatch')
        records = tuple(PhaseTimingRecord.from_payload(payload) for payload in receipt['phase_timings'])
        require(all(not record.cached for record in records), 'Cached duration cannot enter measured summary')
        phases = PhaseTimingRecord.seconds_by_phase(records)
        phase_counts = Counter(record.phase.name for record in records)
        total_seconds = additive_phase_total_seconds({name:seconds for name,seconds in phases.items() if name in ('SUBMIT_OPENHCS','WAIT_OPENHCS')})
        require(phase_counts['SUBMIT_OPENHCS'] == phase_counts['WAIT_OPENHCS'] == 2, 'Require compile+execute disjoint client phases')
        require(math.isclose(phases['SERVER_PIPELINE_JOB'], c['server_job_seconds'], abs_tol=1e-9), 'Server duration mismatch')
        require(math.isclose(c['server_job_completed_at_epoch_seconds']-c['server_job_started_at_epoch_seconds'],c['server_job_seconds'],abs_tol=1e-9), 'Server clock mismatch')
        rows.append({'repetition':rep,'native_execution_seconds':n['pipeline_execution_seconds'] if concurrent is None else concurrent[rep]['pipeline_execution_makespan_seconds'],'native_total_seconds':n['invocation_seconds'] if concurrent is None else concurrent[rep]['invocation_through_completion_makespan_seconds'],'openhcs_execution_seconds':c['server_job_seconds'],'openhcs_total_seconds':total_seconds,'openhcs_compile_seconds':phases['SERVER_COMPILATION_JOB'],'openhcs_axis_only_seconds':phases['EXECUTE_OPENHCS'],'openhcs_first_axis_to_completion_seconds':c['first_axis_through_server_completion_seconds']})
        receipts.append({'path':str(receipt_path),'sha256':sha(receipt_path),'execution_id':c['execution_id']})
        environments.append(receipt['server_environment'])
    require(all(env == environments[0] for env in environments), 'Dependency/environment mixed across repetitions')
    execution = {'case_name':provenance['case'],'assay_category':'','module_category':'','n':repetitions,'equivalent_count':repetitions,'median_native_execution_seconds':median([r['native_execution_seconds'] for r in rows]),'median_openhcs_execution_seconds':median([r['openhcs_execution_seconds'] for r in rows]),'median_native_total_phase_seconds':median([r['native_total_seconds'] for r in rows]),'median_openhcs_total_phase_seconds':median([r['openhcs_total_seconds'] for r in rows]),'median_native_peak_memory_mb':'','median_openhcs_peak_memory_mb':'','min_parity_accuracy':1.0,'speedup_target':SPEEDUP_TARGET}
    execution['median_speedup'] = execution['median_native_execution_seconds']/execution['median_openhcs_execution_seconds']
    execution['median_total_phase_speedup'] = execution['median_native_total_phase_seconds']/execution['median_openhcs_total_phase_seconds']
    execution['meets_execution_speedup_target'] = execution['median_speedup'] >= SPEEDUP_TARGET
    execution['meets_total_phase_speedup_target'] = execution['median_total_phase_speedup'] >= SPEEDUP_TARGET
    total = {**execution,'median_native_execution_seconds':execution['median_native_total_phase_seconds'],'median_openhcs_execution_seconds':execution['median_openhcs_total_phase_seconds'],'median_speedup':execution['median_total_phase_speedup']}
    metadata = {'case':provenance['case'],'source_commit':source_commit,'rows':rows,'receipts':receipts,'raw_inputs':{str(p):sha(p) for p in (provenance_path,native_path,candidate_path)},'server_environment':environments[0],'native_environment':native['environment'],'thread_environment':provenance['thread_environment']}
    metadata['mode'] = {key: provenance[key] for key in ('wells', 'selected_source_wells', 'assignment_scope', 'native_job_count', 'candidate_worker_count', 'candidate_worker_start_method')}
    if scaling:
        metadata['raw_inputs'].update(shard_inputs)
        metadata['native_shard_environments'] = [report['environment'] for report in shard_reports]
    return execution,total,metadata

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--suite-dir',type=Path,required=True)
    parser.add_argument('--output-dir',type=Path,required=True)
    parser.add_argument('--scaling', action='store_true', help='Qualify actual command-declared repeated assignments and concurrent native/OH workers; default remains full-manifest singlewell headline.')
    args=parser.parse_args()
    command=load(args.suite_dir/'command.json')
    terminal_path=args.suite_dir/'terminal.json'
    terminal=load(terminal_path)
    source_commit=command['source_freeze_head']
    require(terminal['returncode']==0 and terminal['source_head_before']==terminal['source_head_after']==source_commit and not terminal['source_status_after'].strip(),'Suite failed or source changed')
    argv=command['argv']
    require(args.scaling or '--all-cases' in argv,'Full manifest suite required')
    repetitions=int(argv[argv.index('--repetitions')+1])
    manifest_path=Path(argv[argv.index('--manifest')+1])
    cases=load(manifest_path)['cases']
    if args.scaling and '--all-cases' not in argv:
        selected = argv[argv.index('--case') + 1]
        cases = [case for case in cases if case['name'] == selected]
        require(len(cases) == 1, 'Scaling command case absent/ambiguous in manifest')
    output_root = Path(argv[argv.index('--output-dir') + 1])
    converted=[convert(output_root / case['name'] if '--all-cases' in argv else output_root, source_commit, repetitions, scaling=args.scaling, command=command) for case in cases]
    require([metadata['case'] for _, _, metadata in converted] == [case['name'] for case in cases], 'Case reports differ from command manifest declarations')
    require(len({m['case'] for _,_,m in converted})==len(converted),'Duplicate case')
    require(all(m['server_environment']==converted[0][2]['server_environment'] and {k:v for k,v in m['native_environment'].items() if k!='temporary_root'}=={k:v for k,v in converted[0][2]['native_environment'].items() if k!='temporary_root'} and m['thread_environment']==converted[0][2]['thread_environment'] for _,_,m in converted),'Source/dependencies/environment mixed across case matrix')
    require(not args.output_dir.exists(),'Fresh summary namespace required')
    args.output_dir.mkdir(parents=True)
    for name,index in (('execution_summary.csv',0),('total_summary.csv',1)):
        rows=[item[index] for item in converted]
        with (args.output_dir/name).open('w',newline='') as handle:
            writer=csv.DictWriter(handle,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    manifest={'status':'PASS','source_head':source_commit,'suite_terminal':{'path':str(terminal_path),'sha256':sha(terminal_path)},'manifest':{'path':str(manifest_path),'sha256':sha(manifest_path)},'converter_sha256':sha(Path(__file__)),'execution_clock':'CP pipeline call including prepare_run, prepare_group, modules and post_run / OH full SERVER_PIPELINE_JOB including plate exports','total_clock':'CP measured invocation / OH sum of disjoint compile+execute SUBMIT+WAIT phases, excluding startup and SCI','speedup_definition':'Ratio of per-engine medians; warmup repetition -1 excluded','memory':'Not measured in matched reports; left absent','cases':[m for _,_,m in converted]}
    if args.scaling:
        if int(argv[argv.index('--native-jobs') + 1]) > 1:
            manifest['execution_clock'] = 'CP actual concurrent pipeline-start through post-run makespan / OH full SERVER_PIPELINE_JOB including plate exports'
            manifest['total_clock'] = 'CP actual concurrent invocation-through-completion makespan / OH sum of disjoint compile+execute SUBMIT+WAIT phases, excluding startup and SCI'
        manifest['assignment_scope'] = 'Independent repeated source assignments, not additional genuine wells'
    (args.output_dir/'summary_custody.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'status':'PASS','cases':len(converted),'output_dir':str(args.output_dir)}))

if __name__=='__main__':main()
