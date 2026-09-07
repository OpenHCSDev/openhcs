"""Real MCP transport remains responsive through post-generation inspection."""

import pytest

from openhcs.mcp import dev_client
from openhcs.mcp.dev_client_commanding import McpDevCommandSpec
from openhcs.mcp.dev_client_core import McpDevServerSpec

_DELAYED_INSPECTION_SERVER = """
import sys
import time
from openhcs.agent.capabilities import GenerateSyntheticPlateCapability
from openhcs.agent.services.plate_inspection_service import PlateInspectionService
from openhcs.mcp.bootstrap import main
from polystore import ensure_storage_registry

# Accelerate an existing declared heartbeat, never introduce one for the test.
if GenerateSyntheticPlateCapability.progress_heartbeat_seconds is not None:
    GenerateSyntheticPlateCapability.progress_heartbeat_seconds = 0.05
original_inspect = PlateInspectionService.inspect

def delayed_inspect(self, request):
    result = original_inspect(self, request)
    print("Post-generation inspection result ready; exercising delayed completion", file=sys.stderr, flush=True)
    time.sleep(1.0)
    return result

PlateInspectionService.inspect = delayed_inspect
# Isolate the injected post-inspection stall from cold storage imports.
ensure_storage_registry()
main(["--surface", "full"])
"""


class _DelayedInspectionServerSpec(McpDevServerSpec):
    heartbeat_enabled = True

    def process_args(self):
        source = _DELAYED_INSPECTION_SERVER
        if not self.heartbeat_enabled:
            source = source.replace(
                "original_inspect =",
                "GenerateSyntheticPlateCapability.progress_heartbeat_seconds = None\noriginal_inspect =",
            )
        return ("-c", source)


@pytest.mark.parametrize("heartbeat_enabled", (False, True))
def test_real_mcp_generation_survives_post_inspection_inactivity_window(
    monkeypatch, tmp_path, heartbeat_enabled
):
    monkeypatch.setattr(
        _DelayedInspectionServerSpec, "heartbeat_enabled", heartbeat_enabled
    )
    monkeypatch.setattr(dev_client, "McpDevServerSpec", _DelayedInspectionServerSpec)
    command_type = type(McpDevCommandSpec.for_name("generate-synthetic-plate"))
    monkeypatch.setattr(command_type, "default_timeout_seconds", 0.5)
    monkeypatch.setenv("OPENHCS_CPU_ONLY", "true")
    monkeypatch.setenv("OPENHCS_AGENT_WRITE_ROOTS", str(tmp_path))
    monkeypatch.setenv("OPENHCS_AGENT_READ_ROOTS", str(tmp_path))
    with dev_client.McpDevClient() as client:
        result = client.execute(
            [
                "generate-synthetic-plate",
                str(tmp_path / "plate"),
                "--grid-rows",
                "1",
                "--grid-cols",
                "1",
                "--tile-width",
                "32",
                "--tile-height",
                "32",
                "--wavelengths",
                "2",
                "--z-stack-levels",
                "1",
                "--num-cells",
                "4",
                "--well",
                "A01",
                "--random-seed",
                "7",
                "--json",
            ],
            timeout_seconds=0.5,
        )
    if not heartbeat_enabled:
        assert result.returncode != 0
        assert "TimeoutError" in result.rendered_output
        assert "exercising delayed completion" in result.server_stderr_tail
        return
    assert result.returncode == 0, result.payload
    generated = result.payload["results"][0]["payloads"][0]
    assert generated["errors"] == []
    assert generated["image_count"] == 2
    assert generated["detected_microscope_type"] == "imagexpress"
    assert result.server_stderr_tail is not None
    assert "exercising delayed completion" in result.server_stderr_tail
    assert "Generate synthetic plate: still running" in result.server_stderr_tail
