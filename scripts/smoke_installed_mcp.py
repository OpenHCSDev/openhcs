"""Smoke-test an installed OpenHCS MCP wheel from outside its source checkout."""

from __future__ import annotations

import argparse
import asyncio
import importlib.util
import json
import os
import shutil
import sys
import tempfile
from collections.abc import Sequence
from importlib.metadata import distribution
from pathlib import Path


def _load_installed_console_scripts() -> tuple[str, ...]:
    """Load every console script declared by the installed OpenHCS wheel."""
    entry_points = tuple(
        entry_point
        for entry_point in distribution("openhcs").entry_points
        if entry_point.group == "console_scripts"
    )
    if not entry_points:
        raise AssertionError("Installed OpenHCS distribution has no console scripts.")
    executable_search_path = os.pathsep.join(
        (str(Path(sys.executable).parent), os.environ.get("PATH", ""))
    )
    for entry_point in entry_points:
        if shutil.which(entry_point.name, path=executable_search_path) is None:
            raise AssertionError(
                f"Installed console script is missing: {entry_point.name}"
            )
        loaded = entry_point.load()
        if not callable(loaded):
            raise AssertionError(
                f"Installed console script does not resolve to a callable: "
                f"{entry_point.name}={entry_point.value}"
            )
    return tuple(sorted(entry_point.name for entry_point in entry_points))


def _tool_payload(result) -> dict:
    if not result.content or not hasattr(result.content[0], "text"):
        raise AssertionError("MCP tool result did not contain text content.")
    payload = json.loads(result.content[0].text)
    if not isinstance(payload, dict):
        raise AssertionError("MCP tool result payload was not an object.")
    if not isinstance(result.structuredContent, dict):
        raise AssertionError("MCP tool result did not contain structured content.")
    if payload != result.structuredContent:
        raise AssertionError("MCP text and structured tool payloads diverged.")
    return payload


async def _run_protocol_smoke() -> dict:
    from mcp import ClientSession, StdioServerParameters
    from mcp.client.stdio import stdio_client

    parameters = StdioServerParameters(
        command=sys.executable,
        args=("-m", "openhcs.mcp"),
    )
    async with stdio_client(parameters) as (read_stream, write_stream):
        async with ClientSession(read_stream, write_stream) as session:
            await asyncio.wait_for(session.initialize(), timeout=30)
            tools_result = await asyncio.wait_for(session.list_tools(), timeout=30)
            health_result = await asyncio.wait_for(
                session.call_tool("openhcs_health_check", {}),
                timeout=30,
            )
            catalog_result = await asyncio.wait_for(
                session.call_tool("openhcs_list_knowledge_documents", {}),
                timeout=30,
            )
            capabilities_result = await asyncio.wait_for(
                session.call_tool("openhcs_list_capabilities", {}),
                timeout=30,
            )
            document_result = await asyncio.wait_for(
                session.call_tool(
                    "openhcs_get_knowledge_document",
                    {
                        "document_id": "openhcs_core_model",
                        "max_chars": 1_000,
                    },
                ),
                timeout=30,
            )

            catalog = _tool_payload(catalog_result)
            document_ids = tuple(
                sorted(
                    item["document_id"]
                    for item in catalog.get("documents", ())
                    if isinstance(item, dict)
                    and isinstance(item.get("document_id"), str)
                )
            )
            if not document_ids:
                raise AssertionError(f"Installed knowledge catalog is empty: {catalog}")
            document_results = {
                document_id: _tool_payload(
                    await asyncio.wait_for(
                        session.call_tool(
                            "openhcs_get_knowledge_document",
                            {
                                "document_id": document_id,
                                "max_chars": 1,
                            },
                        ),
                        timeout=30,
                    )
                )
                for document_id in document_ids
            }
            example_document = document_results["openhcs_example_corpus_map"]
            example_source_sections = tuple(
                section
                for section in example_document["sections"]
                if section["title"].endswith(".py")
            )
            if not example_source_sections:
                raise AssertionError(
                    "Installed knowledge document exposes no native Python examples."
                )
            for section in example_source_sections:
                source = _tool_payload(
                    await asyncio.wait_for(
                        session.call_tool(
                            "openhcs_get_knowledge_document",
                            {
                                "document_id": "openhcs_example_corpus_map",
                                "section_id": section["section_id"],
                                "max_chars": 50_000,
                            },
                        ),
                        timeout=30,
                    )
                )
                if (
                    source["errors"]
                    or ".. code-block:: python" not in source["content"]
                ):
                    raise AssertionError(
                        f"Installed native example source is unreadable: {source}"
                    )

    health = _tool_payload(health_result)
    capabilities = _tool_payload(capabilities_result)
    document = _tool_payload(document_result)
    if health.get("status") != "ok":
        raise AssertionError(f"Installed MCP health failed: {health}")
    installed_version = distribution("openhcs").version
    if health.get("openhcs_version") != installed_version:
        raise AssertionError(
            "Installed MCP health version diverged from wheel metadata: "
            f"health={health.get('openhcs_version')} wheel={installed_version}"
        )
    if not health.get("packaged_resources_ready"):
        raise AssertionError(f"Installed MCP resources are incomplete: {health}")
    if health.get("missing_packaged_resource_paths"):
        raise AssertionError(f"Installed MCP resources are missing: {health}")
    if capabilities.get("surface_profile") != "desktop":
        raise AssertionError(
            f"Installed MCP did not select the desktop surface: {capabilities}"
        )
    declared_tool_names = {
        item.get("name")
        for item in capabilities.get("capabilities", ())
        if isinstance(item, dict) and item.get("kind") == "tool"
    }
    listed_tool_names = {tool.name for tool in tools_result.tools}
    if listed_tool_names != declared_tool_names:
        raise AssertionError(
            "Installed MCP tools diverged from capability discovery: "
            f"listed={listed_tool_names} declared={declared_tool_names}"
        )
    if not all(tool.outputSchema for tool in tools_result.tools):
        raise AssertionError("Installed MCP tools are missing output schemas.")
    if "openhcs_core_model" not in document_ids:
        raise AssertionError(f"Installed knowledge catalog is incomplete: {catalog}")
    if "OpenHCS" not in str(document.get("content", "")):
        raise AssertionError(f"Installed knowledge document is empty: {document}")
    if document.get("errors"):
        raise AssertionError(
            f"Installed knowledge document returned errors: {document}"
        )
    unreadable_documents = {
        document_id: payload
        for document_id, payload in document_results.items()
        if payload.get("errors") or not payload.get("content")
    }
    if unreadable_documents:
        raise AssertionError(
            "Installed knowledge resources are unreadable: " f"{unreadable_documents}"
        )
    return {
        "health_status": health["status"],
        "openhcs_version": installed_version,
        "packaged_resource_count": health.get("packaged_resource_count"),
        "mcp_surface_profile": capabilities["surface_profile"],
        "mcp_tool_count": len(listed_tool_names),
        "knowledge_document_count": len(document_results),
        "native_example_source_count": len(example_source_sections),
        "knowledge_document": "openhcs_core_model",
    }


async def _run_measured_execution_protocol_smoke(session, output_dir: Path) -> dict:
    """Complete one ordinary source-backed job through the installed MCP process."""

    from benchmark.contracts.run_artifacts import MeasuredPipelineRunArtifact
    from openhcs.core.config import PipelineConfig
    from openhcs.core.pipeline_document import PipelineDocumentAuthority
    from openhcs.core.steps import FunctionStep
    from openhcs.processing.backends.processors.numpy_processor import gaussian_blur

    plate = output_dir / "protocol_plate"
    generated = _tool_payload(
        await asyncio.wait_for(
            session.call_tool(
                "openhcs_generate_synthetic_plate",
                {
                    "output_dir": str(plate),
                    "grid_rows": 1,
                    "grid_cols": 1,
                    "tile_width": 32,
                    "tile_height": 32,
                    "wavelengths": 1,
                    "z_stack_levels": 1,
                    "num_cells": 2,
                    "wells": ["A01"],
                    "format": "ImageXpress",
                    "random_seed": 7,
                },
            ),
            timeout=90,
        )
    )
    if not plate.is_dir() or generated.get("errors"):
        raise AssertionError(f"Installed MCP did not generate a plate: {generated}")

    document = PipelineDocumentAuthority.from_values(
        pipeline_config=PipelineConfig(),
        pipeline_steps=[
            FunctionStep(name="Blur", func=(gaussian_blur, {"sigma": 1.0}))
        ],
    )
    created = _tool_payload(
        await asyncio.wait_for(
            session.call_tool(
                "openhcs_create_orchestrator_session_from_pipeline_source",
                {
                    "plate_path": str(plate),
                    "pipeline_source": PipelineDocumentAuthority.render(document),
                    "port": 26000 + os.getpid() % 20000,
                    "persistent": False,
                },
            ),
            timeout=90,
        )
    )
    session_id = created.get("session_id")
    if not isinstance(session_id, str):
        raise AssertionError(f"Installed MCP did not create a session: {created}")

    evidence_dir = output_dir / "measured"
    evidence_dir.mkdir()
    status = _tool_payload(
        await asyncio.wait_for(
            session.call_tool(
                "openhcs_submit_pipeline_execution",
                {
                    "session_id": session_id,
                    "runtime_observation_export_path": str(
                        MeasuredPipelineRunArtifact.RUNTIME_OBSERVATION.path_in(
                            evidence_dir
                        )
                    ),
                    "wait": True,
                    "submit_timeout_ms": 120_000,
                    "wait_timeout_ms": 120_000,
                },
            ),
            timeout=180,
        )
    )
    if status.get("status") != "complete" or not isinstance(status.get("job_id"), str):
        raise AssertionError(f"Installed MCP execution did not complete: {status}")

    finalized = _tool_payload(
        await asyncio.wait_for(
            session.call_tool(
                "openhcs_finalize_measured_pipeline_run",
                {
                    "job_id": status["job_id"],
                    "run_id": "installed-protocol-smoke",
                    "pipeline_name": "Blur",
                },
            ),
            timeout=90,
        )
    )
    inspected = _tool_payload(
        await asyncio.wait_for(
            session.call_tool(
                "openhcs_inspect_measured_pipeline_run",
                {"output_dir": str(evidence_dir)},
            ),
            timeout=90,
        )
    )
    if finalized.get("execution_id") != status.get("server_execution_id"):
        raise AssertionError(f"Installed MCP receipt changed job identity: {finalized}")
    if not inspected.get("source_evidence") or any(
        not item.get("valid") for item in inspected["source_evidence"]
    ):
        raise AssertionError(f"Installed MCP retained invalid evidence: {inspected}")
    return {"measured_execution_id": finalized["execution_id"]}


async def _run_benchmark_protocol_smoke(
    output_dir: Path, *, exercise_measured_execution: bool = False
) -> dict:
    """Prove the installed expert extension through a fresh MCP client."""

    from mcp import ClientSession, StdioServerParameters
    from mcp.client.stdio import stdio_client

    from openhcs.agent.path_policy import AgentPathPolicy

    manifest_path = output_dir / "empty_benchmark_manifest.json"
    manifest_path.write_text('{"cases": []}\n', encoding="utf-8")

    parameters = StdioServerParameters(
        command=sys.executable,
        args=("-m", "openhcs.mcp", "--surface", "full"),
        env={
            AgentPathPolicy.readable_roots_environment_key: str(output_dir),
            AgentPathPolicy.writable_roots_environment_key: str(output_dir),
        },
    )
    async with stdio_client(parameters) as (read_stream, write_stream):
        async with ClientSession(read_stream, write_stream) as session:
            await asyncio.wait_for(session.initialize(), timeout=60)
            listed = await asyncio.wait_for(session.list_tools(), timeout=60)
            capabilities = _tool_payload(
                await asyncio.wait_for(
                    session.call_tool("openhcs_list_capabilities", {}), timeout=60
                )
            )
            callable_read_only = {
                "openhcs_list_benchmark_cases",
                "openhcs_inspect_measured_pipeline_run",
                "openhcs_report_measured_pipeline_run",
            }
            expected = callable_read_only | {"openhcs_finalize_measured_pipeline_run"}
            listed_names = {tool.name for tool in listed.tools}
            declared_names = {
                item.get("name")
                for item in capabilities.get("capabilities", ())
                if isinstance(item, dict) and item.get("kind") == "tool"
            }
            if capabilities.get("surface_profile") != "full":
                raise AssertionError(
                    f"Installed benchmark MCP surface was not full: {capabilities}"
                )
            if not expected <= listed_names & declared_names:
                raise AssertionError(
                    "Installed benchmark tools are not both declared and listed: "
                    f"expected={expected} listed={listed_names} declared={declared_names}"
                )
            for name in callable_read_only:
                request = (
                    {"manifest_path": str(manifest_path)}
                    if name == "openhcs_list_benchmark_cases"
                    else {"output_dir": str(output_dir)}
                )
                result = await asyncio.wait_for(
                    session.call_tool(name, request),
                    timeout=60,
                )
                if result.isError:
                    raise AssertionError(f"Installed benchmark tool failed: {name}")
                payload = _tool_payload(result)
                if name == "openhcs_list_benchmark_cases":
                    if payload.get("manifest_path") != str(manifest_path):
                        raise AssertionError(
                            f"Installed benchmark discovery used the wrong manifest: {payload}"
                        )
                    if payload.get("cases") != [] or payload.get("warnings") != []:
                        raise AssertionError(
                            f"Installed empty benchmark discovery is invalid: {payload}"
                        )
                    continue
                if payload.get("output_dir") != str(output_dir):
                    raise AssertionError(
                        f"Installed benchmark tool inspected the wrong run: {payload}"
                    )
                if not payload.get("warnings"):
                    raise AssertionError(
                        f"Absent receipt was not reported by {name}: {payload}"
                    )
            measured_execution = (
                await _run_measured_execution_protocol_smoke(session, output_dir)
                if exercise_measured_execution
                else {}
            )
    return {"benchmark_expert_tools": sorted(expected), **measured_execution}


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--forbid-import-root",
        type=Path,
        required=True,
        help="Source checkout that must not own the imported openhcs package.",
    )
    parser.add_argument(
        "--exercise-measured-execution",
        action="store_true",
        help="Run one ordinary source-backed job through the installed MCP process.",
    )
    return parser


def assert_not_source_checkout_import(
    *,
    package_path: Path,
    knowledge_root: Path,
    forbidden_root: Path,
) -> None:
    """Reject source-owned resources without rejecting an in-tree venv."""

    source_package_root = forbidden_root / "openhcs"
    if package_path.is_relative_to(source_package_root):
        raise AssertionError(
            "Smoke test imported the source checkout instead of the wheel: "
            f"{package_path}"
        )
    if knowledge_root == forbidden_root:
        raise AssertionError(
            f"Knowledge root resolved into the source checkout: {knowledge_root}"
        )


def main(argv: Sequence[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    forbidden_root = args.forbid_import_root.resolve()
    original_working_directory = Path.cwd()
    from openhcs.agent.path_policy import AgentPathLocationAuthority

    with tempfile.TemporaryDirectory(
        prefix="openhcs-installed-mcp-",
        dir=AgentPathLocationAuthority.temporary_root(),
    ) as directory:
        working_directory = Path(directory).resolve()
        os.chdir(working_directory)
        try:
            import openhcs
            from openhcs.agent.knowledge_manifest import (
                default_knowledge_base_manifest_path,
                default_repo_root,
            )

            package_path = Path(openhcs.__file__).resolve()
            knowledge_root = default_repo_root().resolve()
            assert_not_source_checkout_import(
                package_path=package_path,
                knowledge_root=knowledge_root,
                forbidden_root=forbidden_root,
            )
            manifest_path = default_knowledge_base_manifest_path()
            if not manifest_path.is_file():
                raise AssertionError(
                    f"Packaged knowledge manifest is missing: {manifest_path}"
                )
            console_scripts = _load_installed_console_scripts()
            if importlib.util.find_spec("PyQt6") is None:
                raise AssertionError(
                    "The combined local client installation is missing the PyQt6 UI."
                )

            result = asyncio.run(_run_protocol_smoke())
            result.update(
                asyncio.run(
                    _run_benchmark_protocol_smoke(
                        working_directory,
                        exercise_measured_execution=args.exercise_measured_execution,
                    )
                )
            )
            result.update(
                {
                    "package_path": str(package_path),
                    "knowledge_root": str(knowledge_root),
                    "console_scripts": console_scripts,
                    "working_directory": str(working_directory),
                }
            )
        finally:
            os.chdir(original_working_directory)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
