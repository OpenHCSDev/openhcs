from __future__ import annotations

import hashlib
import json
import logging
import os
import platform
import shutil
import subprocess
import sys
import time
from dataclasses import replace
from pathlib import Path

import numpy
import scipy
import openhcs
from benchmark.adapters.cellprofiler import (
    CellProfilerRunRequest,
    HeadlessCellProfilerPipelinePolicy,
    NativeCellProfilerInputDomainStrategy,
)
from benchmark.adapters.cppipe_source import resolve_cppipe_source
from benchmark.cellprofiler_comparison import load_comparison_cases
from benchmark.cellprofiler_export_equivalence import cellprofiler_database_export_equivalence
from openhcs.constants.constants import AllComponents
from openhcs.core.config import (
    AnalysisConsolidationConfig,
    GlobalPipelineConfig,
    LazyPathPlanningConfig,
    LazyWellFilterConfig,
    MaterializationBackend,
    PathPlanningConfig,
    VFSConfig,
    WellFilterConfig,
)
from openhcs.core.equivalence.comparison import runtime_image_differences
from openhcs.core.equivalence.outputs import RuntimeOutputSnapshot
from openhcs.core.input_workspace import InputWorkspacePreparationRequest
from openhcs.core.runtime_execution_validation import runtime_artifact_execution_failures
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.core.progress.types import ProgressEvent, ProgressPhase
from openhcs.core.source_matching import source_component_metadata_value
from openhcs.interop.cellprofiler.measurement_dialect import cellprofiler_runtime_equivalence_policy
from openhcs.interop.cellprofiler.plate_workspace import prepare_cellprofiler_input_workspace
from openhcs.runtime.zmq_execution_client import OpenHCSExecutionSubmission, ZMQExecutionClient
from openhcs.runtime.zmq_execution_observation import ZMQRuntimeExecutionObservationExport
from objectstate.lazy_factory import ensure_global_config_context, rebuild_lazy_config_with_new_global_reference
from zmqruntime.execution import ExecutionSubmissionResponse, ExecutionWaitResult
from zmqruntime import DataControlPortPairAuthority, TransportMode
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG


ROOT = Path(sys.argv[1]).resolve()
ROOT.mkdir(parents=True, exist_ok=True)
PROJECT = Path.cwd().resolve()
logging.basicConfig(level=logging.WARNING)
case, = [c for c in load_comparison_cases(PROJECT / 'benchmark/manifests/official30_portable_axis1.json') if c.name == 'cp_tutorial_translocation_final']
prepared = prepare_cellprofiler_input_workspace(InputWorkspacePreparationRequest(
    selected_path=case.dataset_path,
    selected_pipeline_path=case.cppipe_path,
    workspace_root=ROOT / 'source_workspace',
    generated_source_path=ROOT / 'pipeline.py',
))
assert prepared.pipeline_import_error is None, prepared.pipeline_import_error
assert prepared.materialization is not None
assert prepared.pipeline_steps is not None and prepared.pipeline_config is not None
wells = tuple(sorted({source_component_metadata_value(m, AllComponents.WELL) for m in prepared.materialization.source_metadata.values()}))[:8]
assert len(wells) == 8 and None not in wells, wells
global_config = GlobalPipelineConfig(
    num_workers=1,
    use_threading=False,
    well_filter_config=WellFilterConfig(well_filter=list(wells)),
    path_planning_config=PathPlanningConfig(global_output_folder=ROOT / 'candidate', output_dir_suffix='_matched_pilot'),
    vfs_config=VFSConfig(materialization_backend=MaterializationBackend.DISK),
    analysis_consolidation_config=AnalysisConsolidationConfig(enabled=False),
    materialize_runtime_artifacts=False,
)
ensure_global_config_context(GlobalPipelineConfig, global_config)
pipeline_config = replace(
    prepared.pipeline_config,
    well_filter_config=LazyWellFilterConfig(well_filter=list(wells)),
    path_planning_config=LazyPathPlanningConfig(global_output_folder=ROOT / 'candidate', output_dir_suffix='_matched_pilot'),
)
pipeline_config = rebuild_lazy_config_with_new_global_reference(pipeline_config, global_config, GlobalPipelineConfig)
native_request = CellProfilerRunRequest(
    dataset_path=case.dataset_path,
    pipeline_name=case.name,
    pipeline_params={'dataset_id': case.resolved_dataset_id, 'cppipe_path': str(case.cppipe_path)},
    metrics=(),
    output_dir=ROOT / 'native_preparation',
    global_config=global_config,
)
source = resolve_cppipe_source(native_request.cppipe_source)
execution_path = HeadlessCellProfilerPipelinePolicy.execution_path(source.path, native_request.output_dir)
native_domain = NativeCellProfilerInputDomainStrategy.select_for(native_request, source).prepare(native_request, source, execution_path)
native_payload = {
    'pipeline_path': str(native_domain.cppipe_path),
    'input_dir': str(native_domain.input_dir),
    'file_list_path': str(native_domain.file_list_path) if native_domain.file_list_path is not None else None,
    'output_root': str(ROOT / 'native'),
    'expected_image_sets': 8,
    'repetitions': 3,
}
(ROOT / 'native_request.json').write_text(json.dumps(native_payload, indent=2))
print('Wells', wells, flush=True)
if (ROOT / 'native_report.json').exists():
    native_report = json.loads((ROOT / 'native_report.json').read_text())
else:
    native_completed = subprocess.run(
        [str(PROJECT / '.venv-cellprofiler39/bin/python'), str(PROJECT / 'benchmark/native_cellprofiler_batch_worker.py'), str(ROOT / 'native_request.json')],
        cwd=PROJECT, env=os.environ.copy(), capture_output=True, text=True, timeout=900,
    )
    (ROOT / 'native_stdout.log').write_text(native_completed.stdout)
    (ROOT / 'native_stderr.log').write_text(native_completed.stderr)
    native_completed.check_returncode()
    native_report = json.loads(native_completed.stdout.splitlines()[-1])
    (ROOT / 'native_report.json').write_text(json.dumps(native_report, indent=2))
print('Native completed', flush=True)
port = DataControlPortPairAuthority.acquire(OPENHCS_ZMQ_CONFIG, transport_mode=TransportMode.TCP).data_port
events = []
client = ZMQExecutionClient(port=port, persistent=False, transport_mode=TransportMode.TCP, progress_callback=lambda event: events.append(dict(event)))
observation_path = ROOT / 'candidate_observation.pkl'
submission = OpenHCSExecutionSubmission(
    plate_id=case.dataset_path,
    execution_plate_id=prepared.execution_plate_path,
    selected_pipeline_path=case.cppipe_path,
    pipeline_document=PipelineDocumentAuthority.from_values(pipeline_config=pipeline_config, pipeline_steps=prepared.pipeline_steps),
    global_config=global_config,
    config_params={'runtime_observation_export_path': str(observation_path)},
)
observations = []
policy = cellprofiler_runtime_equivalence_policy(compare_image_pixels=True)
try:
    with client:
        client.endpoint_compatibility().require_match()
        endpoint = client.connected_endpoint
        output_roots = ()
        for repetition in range(-1, 3):
            for output_root in output_roots:
                assert output_root.is_relative_to(ROOT / 'candidate')
                shutil.rmtree(output_root)
            compilation_started = time.perf_counter()
            compiled = ExecutionSubmissionResponse.from_wire(client.submit_compile(submission))
            artifact_id = compiled.require_execution_id('Pilot compilation')
            ExecutionWaitResult.from_wire(client.wait_for_completion(artifact_id, poll_interval=0.05)).require_complete('Pilot compilation')
            compilation_seconds = time.perf_counter() - compilation_started
            execution_submission = OpenHCSExecutionSubmission(
                plate_id=case.dataset_path, execution_plate_id=prepared.execution_plate_path,
                selected_pipeline_path=case.cppipe_path,
                pipeline_document=submission.pipeline_document,
                global_config=global_config,
                config_params={'runtime_observation_export_path': str(observation_path)},
                compile_artifact_id=artifact_id,
            )
            events.clear()
            started_wall = time.time()
            started = time.perf_counter()
            response = ExecutionSubmissionResponse.from_wire(client.submit_pipeline(execution_submission))
            execution_id = response.require_execution_id('Pilot execution')
            ExecutionWaitResult.from_wire(client.wait_for_completion(execution_id, poll_interval=0.05)).require_complete('Pilot execution')
            completed = time.perf_counter()
            completed_wall = time.time()
            (ROOT / ('events_' + str(repetition) + '.json')).write_text(json.dumps(events, indent=2))
            observation = ZMQRuntimeExecutionObservationExport.read(observation_path)
            current_events = [ProgressEvent.from_dict(event) for event in events if event['execution_id'] == execution_id]
            axis_started = min(event.timestamp for event in current_events if event.phase is ProgressPhase.AXIS_STARTED)
            probe_receipt = {
                'repetition': repetition, 'execution_id': execution_id, 'compile_artifact_id': artifact_id,
                'compile_api_seconds': compilation_seconds,
                'invocation_seconds': completed - started,
                'first_axis_through_completion_observed_seconds': completed_wall - axis_started,
                'pre_first_axis_seconds': axis_started - started_wall,
                'axis_count': observation.axis_count,
                'endpoint_pid': endpoint.process_identity.pid,
                'endpoint_log_path': endpoint.log_file_path,
                'endpoint_application_version': endpoint.application.version,
                'output_files': [str(path) for path in observation.exports.output_files],
                'execution_failures': observation.execution_failures(),
                'validation_failures': runtime_artifact_execution_failures(observation.expectation, observation.observation()),
            }
            (ROOT / 'candidate_probe.json').write_text(json.dumps(probe_receipt, indent=2))
            observation.require_valid_observation()
            assert observation.axis_count == 8, observation.axis_count
            output_roots = tuple(Path(path) for path in observation.output_roots)
            native_root = ROOT / 'native' / str(repetition)
            database_report = cellprofiler_database_export_equivalence(native_root, observation.exports, policy=policy)
            native_images = RuntimeOutputSnapshot.from_output_root(native_root).images
            candidate_images = RuntimeOutputSnapshot.from_export_observation(observation.exports).images
            image_differences = runtime_image_differences(native_images, candidate_images, policy)
            assert len(native_images) == len(candidate_images) == 8
            current_events = [ProgressEvent.from_dict(event) for event in events if event['execution_id'] == execution_id]
            axis_started = min(event.timestamp for event in current_events if event.phase is ProgressPhase.AXIS_STARTED)
            row = {
                'repetition': repetition, 'execution_id': execution_id, 'compile_artifact_id': artifact_id,
                'compile_api_seconds': compilation_seconds,
                'invocation_seconds': completed - started,
                'first_axis_through_completion_observed_seconds': completed_wall - axis_started,
                'pre_first_axis_seconds': axis_started - started_wall,
                'axis_count': observation.axis_count,
                'database_differences': [str(d) for d in database_report.differences],
                'image_differences': [str(d) for d in image_differences],
                'image_count': len(candidate_images),
                'output_roots': [str(path) for path in output_roots],
            }
            observations.append(row)
            (ROOT / 'candidate_report.json').write_text(json.dumps(observations, indent=2))
            (ROOT / ('events_' + str(repetition) + '.json')).write_text(json.dumps(events, indent=2))
            print('Candidate', row, flush=True)
finally:
    client.disconnect()
report = {
    'source_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=PROJECT, text=True).strip(),
    'scoped_dirty_diff_sha256': hashlib.sha256(subprocess.check_output(['git', 'diff', '--', 'openhcs/processing/backends/cellprofiler/intensity.py', 'openhcs/processing/backends/cellprofiler/intensity_object_quantiles_numba.py'], cwd=PROJECT)).hexdigest(),
    'case_name': case.name, 'wells': wells, 'concurrency': 1, 'repetitions': 3,
    'candidate_environment': {'python_executable': sys.executable, 'python_version': platform.python_version(), 'openhcs_version': openhcs.__version__, 'numpy_version': numpy.__version__, 'scipy_version': scipy.__version__},
    'thread_environment': {name: os.environ[name] for name in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS', 'VECLIB_MAXIMUM_THREADS', 'NPY_DISABLE_CPU_FEATURES')},
    'native': native_report, 'candidate': observations,
}
(ROOT / 'report.json').write_text(json.dumps(report, indent=2))
