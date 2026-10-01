"""Preparation checks, not a simulated/live/native journey acceptance."""

import ast
import importlib.util
import json
from pathlib import Path
import sys

import pytest


@pytest.fixture
def driver():
    path = Path(__file__).with_name("public_two_vector_388.py")
    spec = importlib.util.spec_from_file_location("paired388_driver", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_offline_oracles(driver):
    driver.offline_check()
    driver.assert_label_identity(tuple(driver.expected_labels()), (64, 64))


def test_actual_original_config_and_step_authoring_boundary(driver):
    from openhcs.agent.dto.config import ConfigPatch
    from openhcs.agent.services.config_service import ConfigService
    from openhcs.agent.services.pipeline_authoring_service import (
        _instantiate_config_patch, _step_config_patches,
    )
    from openhcs.constants.constants import GroupBy, Microscope, VariableComponents

    service = ConfigService()
    result = service.validate_patch("pipeline", ConfigPatch(**driver.pipeline_patch("_classification388_public_pair")))
    assert result.valid, result.errors
    config = service.resolve_ref(result.config_ref)
    assert config.microscope == Microscope.SOURCE_BINDINGS
    assert config.num_workers == 1 and config.materialize_runtime_artifacts
    assert config.source_bindings_config.source_voxel_spacing.values_zyx == (1.3556, 1.3556)
    overrides = _step_config_patches(driver.step_overrides(5992, select_source=True))
    typed = {name: _instantiate_config_patch(patch) for name, patch in overrides.items()}
    assert typed["processing_config"].group_by is GroupBy.NONE
    assert typed["processing_config"].variable_components == [VariableComponents.CHANNEL]
    assert typed["source_bindings"].enabled
    assert typed["napari_streaming_config"].port == 5992
    assert typed["step_materialization_config"].enabled


def test_complete_real_authoring_render_reconstruction_no_fixture_execution(driver, monkeypatch):
    from openhcs.agent.dto.config import ConfigPatch
    from openhcs.agent.dto.pipeline import FunctionStepAddRequest
    from openhcs.agent.services.config_service import ConfigService
    from openhcs.agent.services.pipeline_authoring_service import PipelineAuthoringService
    from openhcs.core.function_patterns import normalize_function_pattern
    from openhcs.core.pipeline_document import PipelineDocumentAuthority
    from openhcs.processing.backends.cellprofiler.classification import (
        ClassificationThresholdMethod, classify_objects_two_measurements,
    )
    from openhcs.processing.backends.lib_registry.registry_service import RegistryService
    from tests.unit.agent.test_compile_selector_authoring import SelectedDeclarations

    # Load original declarations only; never invoke the fixture or classifier.
    spec = importlib.util.spec_from_file_location("paired388_original_fixture_declarations", driver.FIXTURE)
    module = importlib.util.module_from_spec(spec)
    monkeypatch.setitem(sys.modules, spec.name, module)
    spec.loader.exec_module(module)
    original_fixture = module.engineering_calibration_classification_fixture
    metadata = dict(RegistryService.declared_metadata_for_callable(func)
                    for func in (original_fixture, classify_objects_two_measurements))
    monkeypatch.setattr(RegistryService, "_metadata_cache", metadata)
    monkeypatch.setattr(RegistryService, "_resolved_reference_callables", {})
    config_service = ConfigService()
    config_ref = config_service.create("pipeline", ConfigPatch(**driver.pipeline_patch("_classification388_public_pair")))
    author = PipelineAuthoringService(SelectedDeclarations(), config_service)
    ref = author.create_pipeline(pipeline_config_id=config_ref.config_id)
    fixture_id, _ = RegistryService.declared_metadata_for_callable(original_fixture)
    pair_id, _ = RegistryService.declared_metadata_for_callable(classify_objects_two_measurements)
    assert pair_id == driver.PAIR_ID
    author.add_function_step_from_request(FunctionStepAddRequest.from_fields(
        pipeline_id=ref.pipeline_id, function_id=fixture_id, name="engineering_fixture",
        step_config_overrides=driver.step_overrides(5992, select_source=True)))
    author.add_function_step_from_request(FunctionStepAddRequest.from_fields(
        pipeline_id=ref.pipeline_id, function_id=pair_id, name=driver.PAIR_STEP,
        kwargs=driver.paired_kwargs(), step_config_overrides=driver.step_overrides(5992)))
    validated = author.validate(ref.pipeline_id)
    assert validated.valid, validated.errors
    for clean in (True, False):
        rendered = author.render_source(ref.pipeline_id, clean=clean)
        document = PipelineDocumentAuthority.from_source(rendered.source)
        assert len(document.pipeline_steps) == 2
        assert document.pipeline_config.source_bindings_config.source_voxel_spacing.values_zyx == (1.3556, 1.3556)
        assert document.pipeline_config.path_planning_config.output_dir_suffix == "_classification388_public_pair"
        step = document.pipeline_steps[1]
        normalized = normalize_function_pattern(step.func)
        entry = next(normalized.iter_items())
        kwargs = entry.kwargs_dict
        assert kwargs["measurement1_feature"] == "pixel_count"
        assert kwargs["measurement2_feature"] == "calibration_um"
        assert kwargs["threshold1_value"] == 100.0
        assert kwargs["threshold2_value"] == 2.0
        assert ClassificationThresholdMethod.CUSTOM.value == kwargs["threshold2_method"]
        assert "retained_image_name" not in kwargs
        assert not {"labels", "measurement1_values", "measurement2_values", "classified_image_rule_indices"} & kwargs.keys()


def test_driver_public_tools_are_original_declarations(driver):
    from openhcs.agent.capabilities import FullLocalCapabilitySurfaceProfile, get_agent_capability
    names = {node.value for node in ast.walk(ast.parse(Path(driver.__file__).read_text()))
             if isinstance(node, ast.Constant) and isinstance(node.value, str)
             and node.value.startswith("openhcs_")}
    assert len(names) >= 20
    for name in names:
        assert get_agent_capability(name).supports_surface_profile(FullLocalCapabilitySurfaceProfile())


def test_real_typed_csv_preview_owner_is_used(driver):
    from openhcs.agent.dto.plate import PlateFileQueryResult, PlateFileQueryRecordSummary, PlateInspectionResultFilePreview
    from openhcs.core.plate_file_inventory import PlateFileKind
    rows = ({"object_label": "1"}, {"object_label": "2"})
    record = PlateFileQueryRecordSummary(kind=PlateFileKind.RESULT, key="rows.csv",
        relative_path="rows.csv", full_path="/owned/rows.csv",
        preview=PlateInspectionResultFilePreview(csv_rows=rows))
    query = PlateFileQueryResult(schema_version="1", plate_path="/owned",
        requested_microscope_type="auto", records=(record,))
    assert driver.csv_preview(query, "rows.csv") == ("/owned/rows.csv", rows)
    from dataclasses import replace
    with pytest.raises(AssertionError, match="truncated"):
        driver.csv_preview(replace(query, truncated_count=1), "rows.csv")
    with pytest.raises(AssertionError, match="exactly one"):
        driver.csv_preview(replace(query, records=(record, record)), "rows.csv")
    with pytest.raises(AssertionError, match="incomplete"):
        driver.csv_preview(replace(query, records=(replace(record, preview=replace(record.preview, truncated=True)),)), "rows.csv")


def test_original_decoder_recovers_real_public_pipeline_response(driver):
    from openhcs.agent.capabilities import get_agent_capability
    from openhcs.agent.dto.common import SCHEMA_VERSION
    from openhcs.agent.dto.pipeline import PipelineRef
    from openhcs.mcp.dev_client_core import McpDevToolBatchResponse, McpDevToolResult, McpDevServerIdentity
    from openhcs.serialization.json import to_jsonable
    batch = McpDevToolBatchResponse(server=McpDevServerIdentity(command="source-proof-no-spawn", module="openhcs.mcp.server"), results=(McpDevToolResult(
        tool="openhcs_create_pipeline", mcp_error=False,
        payloads=(to_jsonable(PipelineRef("pipeline-proof", "openhcs://pipelines/pipeline-proof")),)),))
    decoded = McpDevToolBatchResponse.for_rendering(json.loads(json.dumps(to_jsonable(batch))))
    result = decoded.payload_for(get_agent_capability("openhcs_create_pipeline"))
    assert isinstance(result, PipelineRef)
    assert result.pipeline_id == "pipeline-proof"
    assert SCHEMA_VERSION


@pytest.mark.parametrize("pending_observations", (0, 3))
def test_same_handle_warm_and_cold_readiness_has_no_elapsed_terminal_cutoff(driver, monkeypatch, pending_observations):
    from types import SimpleNamespace
    from openhcs.agent.dto.common import SCHEMA_VERSION
    from openhcs.agent.dto.execution_connection import ExecutionConnectionSpec
    from openhcs.agent.dto.functions import (
        FunctionCatalogPreparationHandle, FunctionCatalogPreparationOutcome,
        FunctionCatalogPreparationState,
    )
    from zmqruntime.messages import ProcessIdentity
    from zmqruntime.startup import EndpointStartupPhase, EndpointStartupStatus
    from openhcs.serialization.json import to_jsonable

    identity = ProcessIdentity.current()  # This source test process, NOT native.
    handle = FunctionCatalogPreparationHandle(ExecutionConnectionSpec(port=5993), identity)
    progress = EndpointStartupStatus(EndpointStartupPhase.CONNECTED, "original owner preparation progress")
    pending = FunctionCatalogPreparationState(schema_version=SCHEMA_VERSION, handle=handle,
        outcome=FunctionCatalogPreparationOutcome.PENDING, progress=progress)
    ready = FunctionCatalogPreparationState(schema_version=SCHEMA_VERSION, handle=handle,
        outcome=FunctionCatalogPreparationOutcome.READY, progress=progress)
    values = iter([pending] * pending_observations + [ready])
    calls = []
    def call(name, arguments):
        calls.append((name, arguments))
        return next(values)
    journey = driver.PublicJourney(None, None)
    monkeypatch.setattr(journey, "call", call)
    clock = {"seconds": 0.0}
    monkeypatch.setattr(driver.time, "monotonic", lambda: clock["seconds"])
    monkeypatch.setattr(driver.time, "sleep", lambda seconds: clock.update(seconds=clock["seconds"] + 80))
    result = journey.observe_until("openhcs_get_function_catalog_preparation_status", to_jsonable(handle),
        lambda value: value.outcome.ready, lambda value: value.outcome.terminal,
        seconds=None, on_observation=journey.readiness_observer(SimpleNamespace(process_identity=identity),
            "catalog", lambda value: value.require_handle(handle)))
    assert result is ready and len(calls) == pending_observations + 1
    assert clock["seconds"] == 80 * pending_observations
    assert all(arguments == to_jsonable(handle) for name, arguments in calls)
    assert all(name == "openhcs_get_function_catalog_preparation_status" for name, arguments in calls)


def test_readiness_rejects_changed_handle_without_restart(driver, monkeypatch):
    from types import SimpleNamespace
    from openhcs.agent.dto.common import SCHEMA_VERSION
    from openhcs.agent.dto.execution_connection import ExecutionConnectionSpec
    from openhcs.agent.dto.functions import FunctionCatalogPreparationHandle, FunctionCatalogPreparationOutcome, FunctionCatalogPreparationState
    from zmqruntime.messages import ProcessIdentity
    from zmqruntime.startup import EndpointStartupPhase, EndpointStartupStatus
    identity = ProcessIdentity.current()
    expected = FunctionCatalogPreparationHandle(ExecutionConnectionSpec(port=5993), identity)
    changed = FunctionCatalogPreparationHandle(ExecutionConnectionSpec(port=5994), identity)
    value = FunctionCatalogPreparationState(schema_version=SCHEMA_VERSION, handle=changed,
        outcome=FunctionCatalogPreparationOutcome.READY,
        progress=EndpointStartupStatus(EndpointStartupPhase.CONNECTED, "wrong owner"))
    journey = driver.PublicJourney(None, None)
    monkeypatch.setattr(journey, "call", lambda name, arguments: value)
    with pytest.raises(RuntimeError, match="changed owner"):
        journey.observe_until("openhcs_get_function_catalog_preparation_status", {},
            lambda value: value.outcome.ready, lambda value: value.outcome.terminal,
            seconds=None, on_observation=journey.readiness_observer(SimpleNamespace(process_identity=identity),
                "catalog", lambda value: value.require_handle(expected)))
