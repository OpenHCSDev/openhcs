"""One source-native PR256 journey; no install, viewer, replay or foreign attach.

Keep the nonblocking validation lock through exact-owned terminal cleanup.
On any uncertain observation retain this process and original handles for
read-only operator commands; never automatically repeat a mutation.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import inspect
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import traceback
from openhcs.domains.microscopy.axes import Microscopy
from openhcs.microscopes.bioformats import BioFormatsHandler

SOURCE = Path(__file__).resolve().parents[2]
PYTHON = Path('/home/ts/code/projects/openhcs/.venv/bin/python')
LOCK = Path('/home/ts/wt/openhcs-issue-batch-20260929/validation.lock')


def fixture_registration_sources():
    """Project each explicitly named fixture declaration through Python's owner.

    Keep the merged fixture authoritative. Imported helpers keep their original
    identities; each registered source declares exactly one processing function.
    """
    from tests.diagnostics import volume_projection_fixture as fixture

    dependencies = (
        (fixture.select_volume_fixture_planes_v2,
         'ArrayPayload, numpy, ProcessingContract, artifact_outputs, SELECTED_VOLUME, '
         'SelectedPlaneImageOutput, np'),
        (fixture.inspect_volume_fixture_v2,
         'ArrayPayload, numpy, ProcessingContract, artifact_outputs, VOLUME_IMAGE, '
         'VOLUME_LABELS, VOLUME_ROWS, np, '
         'DataclassMeasurementColumnarRows, VolumeProjectionFixtureRow'),
    )
    return tuple(
        (function.__name__,
         f'from tests.diagnostics.volume_projection_fixture import ({imports})\n\n'
         + inspect.getsource(function))
        for function, imports in dependencies
    )


def guard(*, projected_disk_gib: float = 0.5, disk_reserve_gib: float = 2) -> dict:
    result = subprocess.run(
        ['/home/ts/bin/agent-resource-check', '--assert-headroom'],
        capture_output=True, text=True, check=False,
    )
    resources = json.loads(result.stdout)
    # Warning text is not an admission policy: in particular, 20 GiB free
    # is a host notification threshold, not the footprint of this bounded run.
    if (resources['level'] == 'critical' or resources['ram_available_gib'] < 8
            or resources['free_gib']['/home'] < projected_disk_gib + disk_reserve_gib):
        raise RuntimeError(f'Resource gate closed: {resources}')
    return resources


def run(args) -> None:
    assert Path(sys.executable).resolve() == PYTHON.resolve()
    sha = subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=SOURCE, text=True,
    ).strip()
    assert sha == args.expected_sha
    root = args.receipts.resolve()
    assert root.is_relative_to(SOURCE) and not root.exists()
    with LOCK.open('a+') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        resources = guard()
        root.mkdir(parents=True)
        owned = root / 'owned'
        owned.mkdir()
        for key in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS',
                    'NUMEXPR_NUM_THREADS', 'NUMBA_NUM_THREADS', 'BLIS_NUM_THREADS'):
            os.environ[key] = '1'
        os.environ.update(
            OPENHCS_CPU_ONLY='true', OPENHCS_HEADLESS='true',
            OPENHCS_USE_THREADING='true', OPENHCS_SUBPROCESS_NO_GPU='1',
            POLYSTORE_SUBPROCESS_NO_GPU='1', CUDA_VISIBLE_DEVICES='',
            QT_QPA_PLATFORM='offscreen', PYTHONDONTWRITEBYTECODE='1',
            POLYSTORE_IMAGEJ_ALLOW_DOWNLOAD='false',
            POLYSTORE_IMAGEJ_CACHE_ROOT='/home/ts/.cache/polystore/imagej',
            XDG_DATA_HOME=str(owned / 'data'), XDG_CACHE_HOME=str(owned / 'cache'),
            XDG_CONFIG_HOME=str(owned / 'config'), XDG_STATE_HOME=str(owned / 'state'),
            XDG_RUNTIME_DIR=str(owned / 'runtime'),
            NUMBA_CACHE_DIR=str(owned / 'numba'), MPLCONFIGDIR=str(owned / 'matplotlib'),
            OPENHCS_UI_CONFIG_CACHE_FILE=str(owned / 'ui_config.config'),
        )
        receipt = dict(accepted=False, source_sha=sha, driver_pid=os.getpid(),
                       source_live_not_installed=True, resources=resources, calls=[],
                       uncertain_dispatch=None, runtime_terminal=False)

        def save():
            (root / 'journey.json').write_text(json.dumps(receipt, indent=2) + '\n')

        save()
        # Existing declaration-owned setup builds both recorded native modules.
        # No package installation, download or shared source mutation.
        tick = time.monotonic()
        with (root / 'build.txt').open('w') as log:
            build = subprocess.run(
                [str(PYTHON), '-B', 'setup.py', 'build_ext', '--inplace', '-j', '1',
                 '--build-temp', str(root / 'build-temp'),
                 '--build-lib', str(root / 'build-lib')],
                cwd=SOURCE, stdout=log, stderr=subprocess.STDOUT, timeout=60,
            )
        receipt['build'] = dict(exit=build.returncode, seconds=time.monotonic()-tick)
        save()
        assert build.returncode == 0

        from dataclasses import replace
        import importlib
        import openhcs
        import polystore
        import zmqruntime
        import metaclass_registry
        from python_introspect import dataclass_from_mapping
        from zmqruntime.config import TransportMode
        from zmqruntime.messages import ExecutionStatus
        from zmqruntime.transport import TransportEndpoint
        from openhcs.agent.capabilities import agent_capabilities
        from openhcs.agent.dto.execution import (
            RuntimeBootstrapState, RuntimeBootstrapCloseResult,
            ExecutionJobRef, ExecutionJobStatus, OrchestratorSessionRef,
        )
        from openhcs.agent.dto.functions import (
            FunctionCatalogPreparationState, CustomFunctionRegistrationResult,
            FunctionCatalogPage,
        )
        from openhcs.mcp.dev_client import McpDevClient
        from openhcs.mcp.dev_client_core import McpDevServerSpec
        from openhcs.pyqt_gui.config import UIConfig, save_ui_config_sync
        from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG
        from openhcs.runtime.zmq_execution_client import ZMQExecutionClient
        from python_introspect import to_jsonable

        modules = (openhcs, polystore, zmqruntime, metaclass_registry,
                   importlib.import_module('openhcs.core._tabular_native'),
                   importlib.import_module('openhcs.processing.backends.cellprofiler._granularity_native'))
        receipt['imports'] = {module.__name__: module.__file__ for module in modules}
        assert all(Path(module.__file__).resolve().is_relative_to(SOURCE) for module in modules)
        receipt['submodules'] = subprocess.check_output(
            ['git', 'submodule', 'status'], cwd=SOURCE, text=True,
        ).splitlines()
        assert not any(row.startswith(('-', '+', 'U')) for row in receipt['submodules'])
        config = replace(OPENHCS_ZMQ_CONFIG, transport_mode=TransportMode.TCP,
                         client_host='127.0.0.1', server_host='127.0.0.1',
                         default_port=args.port)
        endpoint = TransportEndpoint('127.0.0.1', args.port, TransportMode.TCP)
        assert args.port not in (7777, 7790, 5991)
        assert not endpoint.occupied_ports(config)
        launch_plan = ZMQExecutionClient(port=args.port, host='127.0.0.1',
                                        transport_mode=TransportMode.TCP,
                                        config=config).runtime_launch_plan()
        lock_paths = launch_plan.transport_write_paths
        assert all(not path.exists() for path in lock_paths), 'Preserve existing reservations'
        fixture_root = Path('/home/ts/wt/openhcs-issue-batch-20260929/issue257-synthetic-ome-inputs-20260930')
        fixture_source = SOURCE / 'tests/diagnostics/volume_projection_fixture.py'
        os.environ['OPENHCS_AGENT_READ_ROOTS'] = os.pathsep.join((str(SOURCE), str(fixture_root), *(str(p) for p in lock_paths)))
        os.environ['OPENHCS_AGENT_WRITE_ROOTS'] = os.pathsep.join((str(owned), *(str(p) for p in lock_paths)))
        assert save_ui_config_sync(UIConfig(zmq=config))
        receipt['declared_endpoint_pair'] = list(endpoint.port_pair(config).ports)
        receipt['transport_locks'] = [str(p) for p in lock_paths]
        from polystore.zmq_config import POLYSTORE_ZMQ_CONFIG
        receipt['ack_boundary'] = dict(
            native_config_port=config.shared_ack_port,
            polystore_config_port=POLYSTORE_ZMQ_CONFIG.shared_ack_port,
            canonical_owner='zmqruntime.ack_listener.GlobalAckListener',
            streaming_caller='polystore.streaming._streaming_backend.StreamingBackend',
            bind_host='*', independent_of_execution_pair=True,
            sockets_before=subprocess.check_output(['ss', '-ltnp'], text=True),
            foreign_ack_cleanup='never requested',
        )
        original_image = fixture_root / 'A01/image.ome.tif'
        plate = owned / 'plate'
        plate.mkdir()
        image_path = plate / original_image.name
        import shutil
        shutil.copyfile(original_image, image_path)
        import tifffile
        input_pixels = tifffile.imread(image_path)
        assert input_pixels.shape == (3, 8, 9)
        input_hash = hashlib.sha256(image_path.read_bytes()).hexdigest()
        assert input_hash == '5fc4e6baa8015be4b5ca09356575a2083ed70834f1ff447353e6c116fec248bb'
        assert image_path.read_bytes() == original_image.read_bytes()
        fixture_hash = hashlib.sha256(fixture_source.read_bytes()).hexdigest()
        assert fixture_hash == '9b737ed5e669c6f2325cc4af9ebb0b39b706121478149315474f464e3cc30c80'
        registration_sources = fixture_registration_sources()
        from openhcs.processing.custom_functions.manager import CustomFunctionManager
        manager = CustomFunctionManager(create_storage=False)
        for name, code in registration_sources:
            prepared_source = manager._prepare_source(code)
            assert prepared_source.original_name == name
            (root/f'{name}.py').write_text(code)
        receipt['fixture'] = dict(source=str(fixture_source), input=str(image_path),
                                 original_input=str(original_image),
                                 input_sha256=input_hash, byte_identical_copy=True,
                                 source_sha256=fixture_hash,
                                 plane_selections=[[], [2, 0, 1], [0, 1], [1]],
                                 expected_source_planes=[[0, 1, 2], [2, 0, 1], [2, 0], [0]],
                                 registration_source_hashes={name: hashlib.sha256(code.encode()).hexdigest()
                                                             for name, code in registration_sources},
                                 omitted_controls=[])

        class SourceSpec(McpDevServerSpec):
            mcp_environment_keys = (*McpDevServerSpec.mcp_environment_keys,
                                    'PYTHONPATH', 'MPLCONFIGDIR')

        client = McpDevClient(str(PYTHON), use_resident_server=False,
                              server_stderr=(root / 'mcp-stderr.txt').open('w'),
                              initialize_timeout_seconds=10)
        client.server_spec = SourceSpec(str(PYTHON))
        original_handle = None
        began = time.monotonic()

        def call(name, arguments, result_type=None, *, lifecycle=False):
            if not lifecycle:
                current = guard()
                size = sum(p.stat().st_size for p in root.rglob('*') if p.is_file())
                assert size < 80 * 1024 * 1024, '80MiB artifact bound'
                assert time.monotonic()-began < 240, 'Original finite journey bound'
                receipt['last_resources'] = current
            row = dict(tool=name, arguments=arguments, started_unix=time.time(), status='dispatched')
            receipt['calls'].append(row)
            receipt['uncertain_dispatch'] = len(receipt['calls'])
            save()
            tick = time.monotonic()
            result = client.execute(
                ['--allow-error-payloads', 'call', name, '--arguments',
                 json.dumps(arguments), '--json'], timeout_seconds=10,
            )
            row.update(seconds=time.monotonic()-tick, response=result.payload, status='returned')
            save()
            assert not result.payload['errors'], result.payload
            response = result.payload['results'][0]
            assert not response['mcp_error'], response
            payload = response['payloads'][0]
            if payload.get('errors') and payload['errors'][0]['code'] == 'agent_path_policy_rejected':
                # This specific original path-policy owner rejects before dispatch.
                # Other errors, especially post-dispatch uncertainty, retain handles.
                receipt['uncertain_dispatch'] = None
                save()
            assert not payload.get('errors'), payload
            value = dataclass_from_mapping(result_type, payload) if result_type else payload
            receipt['uncertain_dispatch'] = None
            save()
            print(f'{name}: {row["seconds"]:.3f}s', flush=True)
            return value

        def finish(ref):
            while True:
                state = call(agent_capabilities.get_execution_status.name,
                             dict(job_id=ref.job_id, timeout_ms=1000), ExecutionJobStatus)
                if state.is_terminal:
                    assert state.status == ExecutionStatus.COMPLETE.value, state
                    return state
                time.sleep(0.5)

        try:
            client.start()
            health = call('openhcs_health_check', {})
            assert Path(health['server_source_path']).resolve() == SOURCE/'openhcs/mcp/server.py'
            assert not health['restart_required']
            receipt['mcp_pid'] = health['server_process_id']
            call('openhcs_get_authoring_context', dict(kind='first_use'))
            call('openhcs_search_capabilities', dict(query='owned runtime', limit=10))
            startup = call(agent_capabilities.start_owned_runtime.name,
                           dict(port=args.port, host='127.0.0.1', transport_mode='tcp',
                                timeout_ms=500), RuntimeBootstrapState)
            original_handle = startup.handle
            receipt['bootstrap_handle'] = to_jsonable(original_handle)
            save()
            while not startup.ready:
                assert startup.process_alive is not False, startup
                time.sleep(0.5)
                startup = call(agent_capabilities.observe_owned_runtime.name,
                               dict(handle=to_jsonable(original_handle)), RuntimeBootstrapState)
                assert startup.handle == original_handle
            receipt['bootstrap_ready_seconds'] = time.monotonic()-began
            prepare_started = time.monotonic()
            prepared = call(agent_capabilities.start_function_catalog_preparation.name,
                            dict(port=args.port, host='127.0.0.1', transport_mode='tcp'),
                            FunctionCatalogPreparationState)
            preparation_handle = prepared.handle
            receipt['preparation_handle'] = to_jsonable(preparation_handle)
            while not prepared.outcome.ready:
                assert not prepared.outcome.terminal, prepared
                time.sleep(1)
                prepared = call(agent_capabilities.get_function_catalog_preparation_status.name,
                                to_jsonable(preparation_handle), FunctionCatalogPreparationState)
                assert prepared.handle == preparation_handle
            receipt['preparation_seconds'] = time.monotonic()-prepare_started
            receipt['registrations'] = []
            for name, code in registration_sources:
                registered = call('openhcs_register_custom_function', dict(
                    source_code=code, function_name=name,
                    storage_dir=str(original_handle.launch_plan.storage_dir), persist=True,
                    port=args.port, host='127.0.0.1', transport_mode='tcp',
                ), CustomFunctionRegistrationResult)
                assert registered.registered_count == 1
                assert registered.server_identity == original_handle.process_identity
                [persisted] = registered.source_file_paths
                assert Path(persisted).read_text() == code
                receipt['registrations'].append(to_jsonable(registered))
                page = call('openhcs_search_functions', dict(query=name, limit=5), FunctionCatalogPage)
                assert registered.functions[0].function_id in {entry.function_id for entry in page.items}
                save()
            from openhcs.core.config import (PipelineConfig, LazyPathPlanningConfig,
                                             LazyVFSConfig, MaterializationBackend,
                                             LazyStepMaterializationConfig, LazyProcessingConfig)
            from openhcs.core.pipeline_document import PipelineDocumentCodec
            from openhcs.core.steps.function_step import FunctionStep
            from openhcs.processing.custom_functions import (
                select_volume_fixture_planes_v2, inspect_volume_fixture_v2,
            )
            steps = []
            for case, indices in enumerate(((), (2, 0, 1), (0, 1), (1,))):
                for phase, function in enumerate((select_volume_fixture_planes_v2,
                                                  inspect_volume_fixture_v2, inspect_volume_fixture_v2)):
                    steps.append(FunctionStep(
                        func=((function, dict(plane_indices=indices)) if phase == 0 else function),
                        name=f'ProjectionCase{case}Step{phase}',
                        processing_config=LazyProcessingConfig(variable_components=[Microscopy.ZIndex]),
                        step_materialization_config=LazyStepMaterializationConfig(enabled=True)))
            document = PipelineDocumentCodec.from_values(
                pipeline_config=PipelineConfig(num_workers=1, use_threading=True,
                    dataset_source=BioFormatsHandler,
                    path_planning_config=LazyPathPlanningConfig(global_output_folder=owned/'outputs'),
                    vfs_config=LazyVFSConfig(materialization_backend=MaterializationBackend.DISK)),
                pipeline_steps=steps,
            )
            source = PipelineDocumentCodec.render(document)
            (root/'pipeline.py').write_text(source)
            from openhcs.agent.dto.execution import ArtifactPlanInspection
            inspected = call('openhcs_inspect_pipeline_source_artifact_plan',
                 dict(plate_path=str(image_path.parent), pipeline_source=source), ArtifactPlanInspection)
            receipt['artifact_plan'] = to_jsonable(inspected)
            assert inspected.step_count == 12 and inspected.axis_count == 1
            session = call('openhcs_create_orchestrator_session_from_pipeline_source',
                           dict(plate_path=str(image_path.parent), pipeline_source=source,
                                port=args.port, host='127.0.0.1', transport_mode='tcp'),
                           OrchestratorSessionRef)
            for tool, stage in (('openhcs_submit_compile', 'compile'),
                                ('openhcs_submit_pipeline_execution', 'execution')):
                tick = time.monotonic()
                arguments = dict(session_id=session.session_id, wait=False)
                if stage == 'execution':
                    arguments['runtime_observation_export_path'] = str(owned/'observation.pkl.gz')
                job = call(tool, arguments, ExecutionJobRef)
                receipt[stage] = to_jsonable(finish(job))
                receipt[stage+'_seconds'] = time.monotonic()-tick
                save()
            from tests.diagnostics.owned_bootstrap_readback import verify_volume_publication
            receipt['volume_publication'] = verify_volume_publication(
                owned, image_path, input_pixels, inspected,
            )
            assert hashlib.sha256(image_path.read_bytes()).hexdigest() == input_hash
            assert hashlib.sha256(original_image.read_bytes()).hexdigest() == input_hash
            receipt.update(accepted=True, unchanged_input_sha256=input_hash,
                           registration_mcp_calls=len(registration_sources),
                           registrations_per_declaration=1, no_mutation_replay=True)
            save()
        except BaseException as error:
            receipt['failure'] = dict(type=type(error).__name__, message=str(error),
                                      traceback=traceback.format_exc())
            save()
            print('STOPPED: same handle retained; read-only CLI commands or close-owned only.', flush=True)
            import shlex
            for line in sys.stdin:
                if line.strip() == 'close-owned':
                    receipt['operator_disposition'] = 'Close exact owned handle; no mutation replay.'
                    break
                observed = client.execute(shlex.split(line), timeout_seconds=10)
                receipt.setdefault('same_handle_observations', []).append(observed.payload)
                save()
                print(observed.rendered_output, flush=True)
            else:
                raise RuntimeError('No disposition; retain original handles') from error
        # Cleanup is a distinct authorized lifecycle request, never a source replay.
        if original_handle is not None:
            closed = call(agent_capabilities.close_owned_runtime.name,
                          dict(handle=to_jsonable(original_handle), mode='force', timeout_ms=5000),
                          RuntimeBootstrapCloseResult, lifecycle=True)
            assert closed.handle == original_handle
            assert closed.outcome.succeeded and closed.outcome.endpoint_terminated
            assert original_handle.process_identity.is_alive() is False
            assert not endpoint.occupied_ports(config)
            receipt['close'] = to_jsonable(closed)
        client.close()
        receipt['client_closed'] = True
        receipt['runtime_terminal'] = True
        receipt['sockets_after'] = subprocess.check_output(['ss', '-ltnp'], text=True)
        receipt['total_seconds'] = time.monotonic()-began
        save()
        print(json.dumps(dict(accepted=receipt['accepted'], runtime_terminal=True,
                              receipt=str(root/'journey.json'))), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--receipts', type=Path, required=True)
    parser.add_argument('--expected-sha', required=True)
    parser.add_argument('--port', type=int, default=5963)
    run(parser.parse_args())
