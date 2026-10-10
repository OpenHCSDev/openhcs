"""Original generated MCP declaration and typed pipeline authoring controls."""

import asyncio
import json
from dataclasses import dataclass

import numpy as np

from openhcs.agent.capabilities import (
    AgentCapabilityDeclaration,
    AgentDataclassRequestServiceInvocation,
    ConfigDraftCapability,
)
from openhcs.agent.services.function_catalog_service import FunctionCatalogService
from openhcs.core.config import PipelineConfig
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.core.steps.function_step import FunctionStep
from openhcs.mcp.context import OpenHCSAgentContext
from openhcs.mcp.server import build_server
from openhcs.processing.backends.analysis.neurite_outgrowth import (
    MetaXpressCellBodySettings,
    neurite_outgrowth_metaxpress,
)
from openhcs.processing.backends.lib_registry.registry_service import RegistryService


def test_original_mcp_function_help_and_pipeline_document_retain_declared_control(monkeypatch):
    function_id, metadata = RegistryService.declared_metadata_for_callable(
        neurite_outgrowth_metaxpress
    )
    # Supply the already declared original metadata; never start cold catalog
    # preparation or an installed/native process from a source-only control.
    def declared_metadata(_service, requested_id):
        assert requested_id == function_id
        return metadata

    monkeypatch.setattr(FunctionCatalogService, "_metadata", declared_metadata)
    monkeypatch.setattr(RegistryService, "_metadata_cache", {function_id: metadata})
    built = build_server(OpenHCSAgentContext(function_catalog=FunctionCatalogService()))

    async def describe():
        return await built.call_tool(
            "openhcs_describe_function", {"function_id": function_id}
        )

    content, _structured = asyncio.run(describe())
    detail = json.loads(content[0].text)
    assert "parameters" in detail, detail
    control = next(value for value in detail["parameters"] if value["name"] == "cell_body")
    assert "minimum_inscribed_diameter_px" in control["description"]
    assert "in pixels" in control["description"]
    assert "minimum_inscribed_diameter_px=10" in control["default_repr"]
    settings = MetaXpressCellBodySettings(minimum_inscribed_diameter_px=5.0)
    document = PipelineDocumentCodec.from_values(
        pipeline_config=PipelineConfig(),
        pipeline_steps=[FunctionStep(func=(
            neurite_outgrowth_metaxpress, {"cell_body": settings}
        ))],
    )
    source = PipelineDocumentCodec.render(document)
    restored = PipelineDocumentCodec.from_source(source)
    restored_settings = restored.pipeline_steps[0].func[1]["cell_body"]
    assert restored_settings == settings
    assert restored_settings.minimum_inscribed_diameter_px == 5.0
    assert PipelineDocumentCodec.render(restored) == source


def test_independent_declaration_gets_real_mcp_schema_and_cooperative_validation():
    events = []

    class ValidationAudit:
        def validate(self):
            events.append("before")
            super().validate()
            events.append("after")

    @dataclass(frozen=True)
    class AuditedBodyControls(ValidationAudit, MetaXpressCellBodySettings):
        """Independent audit capability composes original body-control behavior."""

    def validate_and_echo(_context, request):
        request.validate()
        labels = np.zeros((16, 16), dtype=np.int32)
        labels[4:11, 4:12] = 1
        np.testing.assert_array_equal(
            request.contract_candidates(labels, labels * 1200.0, 1.3556),
            [False, True],
        )
        return request

    class BodyGateProbeCapability(ConfigDraftCapability):
        name = "openhcs_test_body_gate_probe"
        title = "Validate independent body controls"
        description = "Source-only automatic schema and cooperative MRO control."
        service = "test_body_controls"
        input_contract = AuditedBodyControls
        output_contract = AuditedBodyControls
        invocation = AgentDataclassRequestServiceInvocation(
            service=lambda context: context,
            method=validate_and_echo,
        )

    try:
        built = build_server()

        async def exercise():
            tools = await built.list_tools()
            probe = next(tool for tool in tools if tool.name == BodyGateProbeCapability.name)
            schema = probe.inputSchema["properties"]["minimum_inscribed_diameter_px"]
            assert schema["type"] == "number"
            assert schema["default"] == 10
            return await built.call_tool(
                BodyGateProbeCapability.name,
                {"minimum_inscribed_diameter_px": 5.0},
            )

        content, _structured = asyncio.run(exercise())
        assert json.loads(content[0].text)["minimum_inscribed_diameter_px"] == 5.0
        assert events == ["before", "after"]
    finally:
        del AgentCapabilityDeclaration.__registry__[BodyGateProbeCapability.name]
