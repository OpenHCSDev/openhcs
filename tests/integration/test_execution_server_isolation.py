"""A real execution client reaches only a server it may use (B7)."""

from __future__ import annotations

import subprocess
import sys
from dataclasses import replace

import psutil
import pytest
from zmqruntime.messages import (
    EndpointLaunch,
    EndpointLaunchMismatchError,
    OwnerOnlyAudience,
    ProcessIdentity,
)

from openhcs.runtime.import_authority import OpenHCSRuntimeImportAuthority
from openhcs.runtime.zmq_execution_client import ZMQExecutionClient

SERVER_START_TIMEOUT_SECONDS = 600
ANOTHER_PROCESS = ProcessIdentity(pid=1, create_time=0.0)


class _ClientOfAnotherCheckout(ZMQExecutionClient):
    def launch(self) -> EndpointLaunch:
        return replace(super().launch(), code_root="/another/checkout")


class _ClientOfAnotherProcess(ZMQExecutionClient):
    def launch(self) -> EndpointLaunch:
        return replace(super().launch(), owner=ANOTHER_PROCESS)


@pytest.fixture(scope="module")
def private_client():
    with ZMQExecutionClient.with_private_server() as client:
        yield client


def test_a_started_server_reports_the_launch_its_client_handed_it(private_client):
    launch = private_client.connected_endpoint.launch

    assert launch == private_client.launch()
    assert launch.code_root == str(
        OpenHCSRuntimeImportAuthority.current().import_root
    )
    assert launch.owner == ProcessIdentity.current()
    assert launch.audience_type is OwnerOnlyAudience
    assert private_client.owned_server_process_is_alive() is True


@pytest.mark.parametrize(
    ("stray_type", "named_in_refusal"),
    [
        (_ClientOfAnotherCheckout, "/another/checkout"),
        (_ClientOfAnotherProcess, "for its own use"),
    ],
)
def test_a_client_from_elsewhere_is_refused_at_the_same_address(
    private_client, stray_type, named_in_refusal
):
    stray = stray_type(persistent=False, config=private_client.config)

    with pytest.raises(EndpointLaunchMismatchError) as refused:
        stray.connect(timeout=10)

    assert named_in_refusal in str(refused.value)
    assert not stray.is_connected()
    assert private_client.owned_server_process_is_alive() is True
    assert private_client.endpoint.ping(private_client.config) is not None


_OWNER_SCRIPT = """
import sys, time
from openhcs._source_dependencies import ensure_source_checkout_external_paths
ensure_source_checkout_external_paths()
from openhcs.runtime.zmq_execution_client import ZMQExecutionClient
with ZMQExecutionClient.with_private_server() as client:
    print(client.connected_endpoint.process_identity.pid, flush=True)
    time.sleep(3600)
"""


@pytest.mark.timeout(SERVER_START_TIMEOUT_SECONDS + 60)
def test_an_execution_server_exits_after_its_owner_is_killed(reap_spawned_processes):
    import_root = str(OpenHCSRuntimeImportAuthority.current().import_root)
    owner = subprocess.Popen(
        [
            sys.executable,
            "-c",
            f"import sys; sys.path.insert(0, {import_root!r})" + _OWNER_SCRIPT,
        ],
        stdout=subprocess.PIPE,
        text=True,
    )
    try:
        server = psutil.Process(int(owner.stdout.readline()))
        workers_and_server = [server, *server.children(recursive=True)]
        assert server.is_running()

        owner.kill()
        owner.wait(timeout=10)

        _gone, alive = psutil.wait_procs(workers_and_server, timeout=30)
        assert alive == []
    finally:
        owner.kill()
