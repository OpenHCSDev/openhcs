"""Continuous real MCP generate/inspect/sample for zero-valued geometry."""

import json
from pathlib import Path

import pytest

from openhcs.mcp.dev_client import McpDevClient


def _payload(client, argv):
    result = client.execute([*argv, "--json"], timeout_seconds=30)
    assert result.returncode == 0, result.rendered_output
    payload = result.payload["results"][0]["payloads"][0]
    assert not payload.get("errors"), payload
    return payload


@pytest.mark.parametrize("format", ("ImageXpress", "OperaPhenix"))
@pytest.mark.parametrize("native", (False, True))
def test_zero_geometry_real_mcp_journey(tmp_path, monkeypatch, format, native):
    monkeypatch.setenv("OPENHCS_CPU_ONLY", "true")
    monkeypatch.setenv("OPENHCS_AGENT_READ_ROOTS", str(tmp_path))
    monkeypatch.setenv("OPENHCS_AGENT_WRITE_ROOTS", str(tmp_path))
    # Explicit owned stdio process: do not reuse or mutate a resident server.
    with McpDevClient(use_resident_server=False) as client:
        _payload(client, ["health"])
        _payload(client, ["authoring-context", "first_use"])
        root = tmp_path / "plate"
        arguments = [
            "generate-synthetic-plate",
            str(root),
            "--grid-rows",
            "1",
            "--grid-cols",
            "1",
            "--tile-width",
            "64",
            "--tile-height",
            "64",
            "--overlap-percent",
            "0",
            "--stage-error-px",
            "0",
            "--wavelengths",
            "1",
            "--z-stack-levels",
            "1",
            "--num-cells",
            "4",
            "--partition-value",
            "A01",
            "--random-seed",
            "7",
            "--format",
            format,
        ]
        if native:
            arguments.append("--openhcs-format")
        generated = _payload(client, arguments)
        assert generated["image_count"] == 1
        assert generated["overlap_percent"] == generated["stage_error_px"] == 0
        inspected = _payload(client, ["inspect-plate", str(root)])
        assert inspected["image_files"]["count"] == 1
        sampled = _payload(
            client,
            [
                "sample-plate-image",
                str(root),
                generated["sampled_image_files"][0],
                "--height",
                "8",
                "--width",
                "8",
                "--include-array-values",
            ],
        )
        assert sampled["sample_shape"] == [8, 8]
        assert sampled["dtype"] == "uint16"
        assert sampled["sample_included"]
        assert sampled["sample_values"]
        if native:
            metadata = json.loads(Path(generated["metadata_file_path"]).read_text())
            assert (
                sum(
                    len(subdir["image_files"])
                    for subdir in metadata["subdirectories"].values()
                )
                == 1
            )
            assert all(
                subdir["grid_dimensions"] == [1, 1]
                for subdir in metadata["subdirectories"].values()
            )
