"""MCP EOF and process-resource closure use the original owning mechanisms."""

import asyncio
from dataclasses import dataclass
import io
from pathlib import Path
import signal
import sys
import threading

import pytest
from polystore import backend_registry
from polystore.bioformats_java import BioFormatsJavaContext

from openhcs.mcp.dev_client_core import McpDevServerSpec, McpDevStdioSession
from openhcs.mcp.execution import McpTransportExecutor


@pytest.mark.parametrize("failure", (None, ValueError("original resource failure")))
def test_original_resource_declaration_and_cooperative_close(monkeypatch, failure):
    calls = []

    class Gateway:
        def dispose(self):
            assert threading.current_thread() is threading.main_thread()
            calls.append("gateway disposed")

    class Java:
        def shutdown_jvm(self):
            assert threading.current_thread() is threading.main_thread()
            calls.append("JVM stopped")

    context = BioFormatsJavaContext(imagej_module=None, scyjava_module=Java())
    context.ij = Gateway()
    monkeypatch.setattr(BioFormatsJavaContext, "_instance", context)
    monkeypatch.setattr(backend_registry, "_cleanup_callbacks", [])
    backend_registry.register_cleanup_callback(BioFormatsJavaContext.shutdown_instance)

    class AuditCloseCapability:
        def close(self):
            calls.append("cooperative enter")
            super().close()
            calls.append("cooperative exit")

    class AuditedExecutor(AuditCloseCapability, McpTransportExecutor):
        pass

    executor = AuditedExecutor()

    def independent_resource():
        assert executor._closed
        assert executor.active_futures() == ()
        assert threading.current_thread() is threading.main_thread()
        calls.append("independent resource")
        if failure is not None:
            raise failure

    # A new resource needs only its original declaration, not an MCP edit.
    backend_registry.register_cleanup_callback(independent_resource)
    backend_registry.register_cleanup_callback(independent_resource)
    if failure is None:
        executor.close()
    else:
        with pytest.raises(ExceptionGroup) as caught:
            executor.close()
        assert caught.value.exceptions == (failure,)
    assert BioFormatsJavaContext._instance is None
    assert context.ij is None
    assert calls[:4] == [
        "cooperative enter", "gateway disposed", "JVM stopped", "independent resource"
    ]
    assert calls.count("cooperative exit") == int(failure is None)
    executor.close()
    assert calls.count("gateway disposed") == 1
    assert calls.count("JVM stopped") == 1
    assert calls.count("independent resource") == 1


def test_off_main_close_rejected_before_resource_release(monkeypatch):
    calls = []
    monkeypatch.setattr(backend_registry, "_cleanup_callbacks", [lambda: calls.append("closed")])
    executor = McpTransportExecutor()
    failures = []

    def attempt():
        try:
            executor.close()
        except RuntimeError as error:
            failures.append(error)

    worker = threading.Thread(target=attempt)
    worker.start()
    worker.join()
    assert len(failures) == 1
    assert "process main thread" in str(failures[0])
    assert not executor._closed
    assert calls == []
    executor.close()
    assert calls == ["closed"]


@dataclass(frozen=True, slots=True, kw_only=True)
class ScriptServerSpec(McpDevServerSpec):
    script: Path

    def process_args(self):
        return ("-u", str(self.script))


@pytest.mark.parametrize("exit_code", (0, 7))
def test_stdio_eof_retains_exact_normal_child_exit(tmp_path, exit_code):
    script = tmp_path / "eof_child.py"
    closed = tmp_path / "closed.txt"
    script.write_text(
        "import sys\nfrom pathlib import Path\n"
        "print('ready', flush=True)\nsys.stdin.read()\n"
        f"Path({str(closed)!r}).write_text('EOF cleanup completed')\n"
        f"sys.exit({exit_code})\n"
    )

    async def journey():
        session = McpDevStdioSession(
            ScriptServerSpec(python_executable=sys.executable, script=script), io.StringIO()
        )
        with (tmp_path / "diagnostic.log").open("w+") as diagnostic:
            session.server_stderr = diagnostic
            async with session:
                process = session.require_process()
                assert await process.stdout.readline() == b"ready\n"
            assert process.returncode == exit_code
            assert closed.read_text() == "EOF cleanup completed"

    asyncio.run(journey())


def test_stdio_stuck_child_uses_unchanged_forced_reap_budget(tmp_path):
    script = tmp_path / "stuck_child.py"
    script.write_text(
        "import signal,sys,time\n"
        "signal.signal(signal.SIGTERM, signal.SIG_IGN)\n"
        "print('ready', flush=True)\nsys.stdin.read()\ntime.sleep(30)\n"
    )

    async def journey():
        with (tmp_path / "diagnostic.log").open("w+") as diagnostic:
            session = McpDevStdioSession(
                ScriptServerSpec(python_executable=sys.executable, script=script), diagnostic
            )
            assert session.teardown_timeout_seconds == 2.0
            async with session:
                process = session.require_process()
                assert await process.stdout.readline() == b"ready\n"
            assert process.returncode == -signal.SIGKILL

    asyncio.run(journey())


@pytest.mark.parametrize("fail_cleanup", (False, True))
def test_real_sdk_stdio_declared_resource_closes_before_child_exit(tmp_path, fail_cleanup):
    from openhcs.runtime.import_authority import OpenHCSRuntimeImportAuthority

    source_root = OpenHCSRuntimeImportAuthority.current().import_root
    script = tmp_path / "declared_resource_server.py"
    closed = tmp_path / "resource-closed.txt"
    script.write_text(
        f"import sys\nsys.path.insert(0, {str(source_root)!r})\n"
        "from pathlib import Path\nimport threading,inspect\n"
        "from mcp.server.fastmcp import FastMCP\n"
        "from polystore import register_cleanup_callback\n"
        "from openhcs.mcp.stdio import McpStdioTransport\n"
        f"assert Path(inspect.getfile(McpStdioTransport)).resolve().is_relative_to(Path({str(source_root)!r}))\n"
        "server = FastMCP('declared-resource-lifetime')\n"
        "@server.tool()\ndef health() -> dict[str, bool]:\n    return {'ok': True}\n"
        "def close_resource():\n"
        "    assert threading.current_thread() is threading.main_thread()\n"
        f"    Path({str(closed)!r}).write_text('main-thread resource closed')\n"
        + ("    raise ValueError('original declared cleanup error')\n" if fail_cleanup else "")
        + "register_cleanup_callback(close_resource)\n"
        "with McpStdioTransport.reserve_process_stdio() as transport:\n"
        "    transport.run(server)\n"
    )

    async def journey():
        with (tmp_path / "sdk-diagnostic.log").open("w+") as diagnostic:
            session = McpDevStdioSession(
                ScriptServerSpec(python_executable=sys.executable, script=script), diagnostic
            )
            async with session:
                process = session.require_process()
                await session.initialize(timeout_seconds=10)
                first = await session.call_tool("health", {}, timeout_seconds=10)
                second = await session.call_tool("health", {}, timeout_seconds=10)
                assert first["structuredContent"] == second["structuredContent"] == {"ok": True}
            assert process.returncode == int(fail_cleanup)
            assert closed.read_text() == "main-thread resource closed"
            diagnostic.seek(0)
            text = diagnostic.read()
            assert "Fatal error" not in text
            assert ("original declared cleanup error" in text) is fail_cleanup
            print("SDK_STDIO_DECLARED_RESOURCE", process.pid, process.returncode, fail_cleanup, flush=True)

    asyncio.run(journey())


def test_resident_connection_close_preserves_resource_until_process_owner_close(monkeypatch, tmp_path):
    from mcp.server.fastmcp import FastMCP
    from pyqt_reactive.services.async_operation_executor import AsyncOperationExecutor
    from openhcs.mcp.dev_client_core import McpDevSocketSession
    from openhcs.mcp.socket import McpSocketTransport, wait_for_socket

    calls = []
    monkeypatch.setattr(backend_registry, "_cleanup_callbacks", [])
    server = FastMCP("resident-process-resource-lifetime")

    @server.tool()
    def health() -> dict[str, bool]:
        return {"ok": True}

    def release_resource():
        assert threading.current_thread() is threading.main_thread()
        calls.append("process resource closed")

    backend_registry.register_cleanup_callback(release_resource)
    transport = McpSocketTransport(tmp_path / "resident.sock")
    clients = AsyncOperationExecutor(max_workers=1)

    async def journey():
        assert await asyncio.to_thread(wait_for_socket, transport.socket_path, timeout_seconds=10)
        try:
            for connection in range(2):
                async with McpDevSocketSession(
                    McpDevServerSpec(sys.executable), io.StringIO(), transport.socket_path
                ) as session:
                    await session.initialize(timeout_seconds=10)
                    result = await session.call_tool("health", {}, timeout_seconds=10)
                    assert result["structuredContent"] == {"ok": True}
                assert calls == [], "A client connection does not own the resident JVM."
        finally:
            transport._stop.set()
            if transport._listener is not None:
                transport._listener.close()

    future = clients.submit(journey)
    try:
        transport.serve(server)
        future.result()
    finally:
        clients.close()
    assert calls == ["process resource closed"]
    transport.execution.close()
    assert calls == ["process resource closed"]
