"""Compilation compatibility must ignore observation, not execution semantics."""

from dataclasses import replace
from pathlib import Path

import pytest

from openhcs.core.debug import DebugExecutionConfig
from openhcs.runtime.zmq_execution_signature import (
    ZMQAuxiliaryExecutionParams,
    ZMQExecutionCompileControl,
    ZMQExecutionConfigTransport,
    ZMQExecutionIdentity,
    ZMQExecutionRequestPayload,
    ZMQRuntimeObservationExportScope,
)


def _payload(config_params=None):
    return ZMQExecutionRequestPayload(
        identity=ZMQExecutionIdentity(
            plate_id="/plate",
            execution_plate_id="/source",
            selected_pipeline_path="/pipeline",
        ),
        pipeline_code="pipeline_config = PipelineConfig()\npipeline_steps = []\n",
        config_transport=ZMQExecutionConfigTransport(config_params=config_params),
        compile_control=ZMQExecutionCompileControl(),
    )


@pytest.mark.parametrize("scope", tuple(ZMQRuntimeObservationExportScope))
@pytest.mark.parametrize("path", ("/evidence/first.pkl.gz", "/evidence/second.pkl.gz"))
def test_observation_options_change_request_but_not_compilation_identity(scope, path):
    options = ZMQAuxiliaryExecutionParams(
        axis_filter=("A01",),
        debug_execution_config=DebugExecutionConfig(debug_session_id="debug-1"),
    )
    compiled = _payload({"unrelated": "keep", **options.to_transport()})
    executed = _payload(
        {
            "unrelated": "keep",
            **replace(
                options,
                runtime_observation_export_path=Path(path),
                runtime_observation_export_scope=scope,
            ).to_transport(),
        }
    )

    assert compiled.request_signature != executed.request_signature
    assert compiled.compilation_signature == executed.compilation_signature
    assert compiled.debug_replay_signature == executed.debug_replay_signature


@pytest.mark.parametrize(
    "config_params",
    (
        {},
        {"runtime_observation_export_path": None},
        {"runtime_observation_export_scope": "values"},
        {"runtime_observation_export_path": "/evidence/values.pkl.gz"},
    ),
)
def test_observation_defaults_do_not_distinguish_compilation(config_params):
    assert (
        _payload().compilation_signature
        == _payload(config_params).compilation_signature
    )


@pytest.mark.parametrize(
    "changed",
    (
        {"well_filter": ["B02"]},
        {"unrelated": "changed"},
        DebugExecutionConfig(debug_session_id="debug-2").to_config_params(),
    ),
)
def test_real_execution_inputs_still_distinguish_compilation(changed):
    compiled = _payload({"well_filter": ["A01"], "unrelated": "keep"})
    executed = _payload({**compiled.config_params, **changed})
    assert compiled.compilation_signature != executed.compilation_signature


@pytest.mark.parametrize(
    "field,value",
    (
        ("plate_id", "/another-plate"),
        ("execution_plate_id", "/another-source"),
        ("selected_pipeline_path", "/another-pipeline"),
    ),
)
def test_source_identities_still_distinguish_compilation(field, value):
    compiled = _payload()
    executed = replace(compiled, identity=replace(compiled.identity, **{field: value}))
    assert compiled.compilation_signature != executed.compilation_signature


def test_pipeline_and_global_configuration_still_distinguish_compilation():
    compiled = _payload()
    assert (
        replace(compiled, pipeline_code="changed").compilation_signature
        != compiled.compilation_signature
    )
    assert (
        replace(
            compiled,
            config_transport=replace(compiled.config_transport, config_code="changed"),
        ).compilation_signature
        != compiled.compilation_signature
    )


def test_invalid_observation_options_are_not_hidden_by_compatibility_projection():
    with pytest.raises(ValueError, match="requires an export path"):
        _payload({"runtime_observation_export_scope": "outcomes"}).compilation_signature
    with pytest.raises(ValueError, match="Unknown runtime observation"):
        _payload({"runtime_observation_export_scope": "invalid"}).compilation_signature
