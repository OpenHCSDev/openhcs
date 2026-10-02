"""Inspection uses existing progress/worker and bundle-root projection owners."""

import asyncio
import sys
import threading
from types import SimpleNamespace

import pytest
from polystore.imagej_distribution import (
    FijiArchiveDistribution,
    ImageJArchiveDownloadPolicy,
)

from openhcs.agent.capabilities import (
    InspectPlatePathCapability,
    ProgressAcknowledgedCapability,
)
from openhcs.agent.dto.common import SCHEMA_VERSION
from openhcs.agent.dto.plate import PlatePathInspectionResult
from openhcs.mcp.dev_client_core import McpDevServerSpec
from openhcs.utils.environment import OpenHCSProcessEnvironment


def test_mcp_launch_preserves_bundle_root_separately_from_run_cache(
    monkeypatch, tmp_path
):
    key = FijiArchiveDistribution.cache_root_environment_key
    bundle_root = str(tmp_path / "bundles")
    run_cache = str(tmp_path / "run-cache")
    monkeypatch.setenv(key, bundle_root)
    download_key = ImageJArchiveDownloadPolicy.allow_download_environment_key
    monkeypatch.setenv(download_key, "false")
    monkeypatch.setenv("XDG_CACHE_HOME", run_cache)
    assert key in OpenHCSProcessEnvironment.child_process_environment_keys()
    environment = McpDevServerSpec(sys.executable).environment()
    assert environment[key] == bundle_root
    assert environment[download_key] == "false"
    assert environment["XDG_CACHE_HOME"] == run_cache


def test_inspection_declares_progress_and_optional_runtime_side_effects():
    capability = InspectPlatePathCapability.to_spec()
    assert (
        capability.progress_heartbeat_seconds
        == ProgressAcknowledgedCapability.progress_heartbeat_seconds
    )
    assert capability.progress_worker_thread_safe
    assert capability.mutating
    assert not capability.read_only
    assert "may_download_verified_fiji_runtime" in capability.side_effects
    assert "Plate contents remain read-only" in capability.description


def test_real_binding_keeps_discovery_read_responsive_during_controlled_cold_io():
    from openhcs.mcp import server

    async def exercise():
        loop = asyncio.get_running_loop()
        entered = asyncio.Event()
        release = threading.Event()
        caller_thread = threading.get_ident()
        observed_threads = []

        class ControlledColdInspection:
            def inspect(self, request):
                observed_threads.append(threading.get_ident())
                loop.call_soon_threadsafe(entered.set)
                assert release.wait(1), "Cold fixture was not released"
                return PlatePathInspectionResult(
                    schema_version=SCHEMA_VERSION,
                    plate_path=request.plate_path,
                    requested_microscope_type=request.microscope_type,
                )

        built = server.build_server(
            SimpleNamespace(plate_inspection_service=ControlledColdInspection())
        )
        pending = asyncio.create_task(
            built.call_tool(
                InspectPlatePathCapability.name, {"plate_path": "/controlled/plate"}
            )
        )
        try:
            await asyncio.wait_for(entered.wait(), 0.5)
            assert not pending.done()
            result = await asyncio.wait_for(
                built.call_tool("openhcs_list_capabilities", {}), 0.5
            )
            assert result is not None
            assert not pending.done(), (
                "Discovery must finish while inspection is still held"
            )
        finally:
            release.set()
            await asyncio.wait_for(pending, 1)
        assert observed_threads and observed_threads[0] != caller_thread

    asyncio.run(exercise())


@pytest.mark.parametrize("fails", (False, True))
def test_existing_progress_reports_held_work_and_propagates_terminal_failure(
    monkeypatch, fails
):
    from openhcs.mcp import server

    monkeypatch.setattr(InspectPlatePathCapability, "progress_heartbeat_seconds", 0.005)

    async def exercise():
        heartbeat = asyncio.Event()
        messages = []
        error = RuntimeError("controlled cold initialization failed")

        class RecordingContext:
            request_context = object()

            async def report_progress(self, progress, total=None, message=None):
                messages.append(message)
                if progress:
                    heartbeat.set()

        async def operation():
            await heartbeat.wait()
            if fails:
                raise error
            return "ready"

        pending = server._await_with_declared_progress(
            InspectPlatePathCapability.to_spec(), RecordingContext(), operation()
        )
        if fails:
            with pytest.raises(RuntimeError) as caught:
                await asyncio.wait_for(pending, 1)
            assert caught.value is error
        else:
            assert await asyncio.wait_for(pending, 1) == "ready"
        assert messages[0] == "Inspect plate path: started"
        assert "Inspect plate path: still running" in messages

    asyncio.run(exercise())
