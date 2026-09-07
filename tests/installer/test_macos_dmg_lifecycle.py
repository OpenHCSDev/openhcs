"""Disk-image ownership, failed detach, and native artifact acceptance."""

from __future__ import annotations

import json
import os
import select
import shlex
import subprocess
import sys
from pathlib import Path

import pytest

LIFECYCLE = (
    Path(__file__).resolve().parents[2] / "packaging/installers/macos/dmg-lifecycle.sh"
)

# The harness executes the shipping shell functions. Only the macOS commands
# are replaced; their recorded plist and device-lifecycle boundary is explicit.
FAKE_COMMAND = r"""
import json
import os
import plistlib
import sys
from pathlib import Path

state_path = Path(os.environ["DMG_TEST_STATE"])
state = json.loads(state_path.read_text())
tool, *args = sys.argv[1:]
with Path(os.environ["DMG_TEST_LOG"]).open("a") as log:
    log.write(json.dumps([tool, *args]) + "\n")

def emit(payload):
    sys.stdout.buffer.write(plistlib.dumps(payload))

if tool == "hdiutil":
    if args[0] == "attach":
        if state["attach_status"]:
            raise SystemExit(state["attach_status"])
        emit({"system-entities": state["entities"]})
    else:
        assert args[0] == "detach"
        assert args[-1] == "/dev/disk4", "Detach must target the whole owned device"
        mode = "force" if "-force" in args else "normal"
        if state[mode + "_removes_disk"]:
            state["attached"] = False
        state_path.write_text(json.dumps(state))
        if state[mode + "_status"]:
            print("hdiutil: couldn't eject disk4 - Resource busy", file=sys.stderr)
        raise SystemExit(state[mode + "_status"])
elif tool == "diskutil":
    assert args[0] == "info"
    if "-plist" in args:
        assert args[-1] == state["requested_mount"]
        emit(state["volume"])
    else:
        # A query error is deliberately independent of actual device presence.
        raise SystemExit(1)
elif tool == "test":
    assert args in [["!", "-e", "/dev/disk4"], ["-e", "/dev/disk4"]]
    # The partition is absent after partial detach; the whole device persists.
    exists = state["attached"]
    raise SystemExit(0 if (not exists if args[0] == "!" else exists) else 1)
elif tool == "plutil":
    payload = plistlib.loads(sys.stdin.buffer.read())
    try:
        for key in args[1].split("."):
            payload = payload[int(key)] if isinstance(payload, list) else payload[key]
    except (KeyError, IndexError):
        raise SystemExit(1)
    print(payload)
elif tool != "sync":
    raise AssertionError(tool)
"""


@pytest.fixture
def lifecycle_harness(tmp_path: Path):
    if sys.platform == "win32":
        pytest.skip("The macOS lifecycle uses a POSIX shell")
    mount_point = tmp_path / "owned mount"
    mount_point.mkdir()
    fake = tmp_path / "macos_command.py"
    fake.write_text(FAKE_COMMAND)
    state = {
        "entities": [
            {"dev-entry": "/dev/disk4s1", "mount-point": str(mount_point)},
            {"dev-entry": "/dev/disk4"},
        ],
        "requested_mount": str(mount_point.resolve()),
        "volume": {
            "MountPoint": str(mount_point.resolve()),
            "ParentWholeDisk": "disk4",
        },
        "attached": True,
        "attach_status": 0,
        "normal_status": 0,
        "normal_removes_disk": True,
        "force_status": 0,
        "force_removes_disk": True,
    }
    state_path, log_path = tmp_path / "state.json", tmp_path / "commands.jsonl"

    def run(operation: str, **changes):
        state.update(changes)
        state_path.write_text(json.dumps(state))
        log_path.write_text("")
        definitions = "\n".join(
            f'function {command}() {{ "$DMG_TEST_PYTHON" "$DMG_TEST_COMMAND" {tool} "$@"; }}'
            for command, tool in (
                ("/usr/bin/hdiutil", "hdiutil"),
                ("/usr/sbin/diskutil", "diskutil"),
                ("/usr/bin/plutil", "plutil"),
                ("/bin/sync", "sync"),
                ("test", "test"),
            )
        )
        script = (
            f"set -euo pipefail\n{definitions}\nsource {shlex.quote(str(LIFECYCLE))}\n"
        )
        script += (
            'mounted_device=$(openhcs_attach_writable_disk_image "owned.dmg" "$DMG_TEST_MOUNT")\n'
            + operation
        )
        result = subprocess.run(
            ["bash", "-c", script],
            env={
                **os.environ,
                "DMG_TEST_PYTHON": sys.executable,
                "DMG_TEST_COMMAND": str(fake),
                "DMG_TEST_STATE": str(state_path),
                "DMG_TEST_LOG": str(log_path),
                "DMG_TEST_MOUNT": str(mount_point),
            },
            capture_output=True,
            text=True,
            timeout=15,
        )
        calls = [json.loads(line) for line in log_path.read_text().splitlines()]
        return result, calls

    return state, run


@pytest.mark.parametrize("reverse_entities", [False, True])
def test_attachment_order_does_not_select_a_partition(
    lifecycle_harness, reverse_entities
):
    state, run = lifecycle_harness
    if reverse_entities:
        state["entities"].reverse()
    result, calls = run('printf "%s\\n" "$mounted_device"')
    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == "/dev/disk4"
    assert ["diskutil", "info", "-plist", state["requested_mount"]] in calls


@pytest.mark.parametrize(
    "volume",
    [
        {"MountPoint": "/", "ParentWholeDisk": "disk0"},
        {"MountPoint": "/Volumes/somebody-else", "ParentWholeDisk": "disk7"},
        {},
    ],
)
def test_incomplete_mount_cannot_resolve_to_the_host_disk(lifecycle_harness, volume):
    _state, run = lifecycle_harness
    result, calls = run('openhcs_detach_disk_image "$mounted_device"', volume=volume)
    assert result.returncode != 0
    assert "did not mount at its owned path" in result.stderr
    assert not any(call[:2] == ["hdiutil", "detach"] for call in calls)


def test_attachment_failure_is_not_reinterpreted_as_an_existing_mount(
    lifecycle_harness,
):
    _state, run = lifecycle_harness
    result, calls = run('openhcs_detach_disk_image "$mounted_device"', attach_status=1)
    assert result.returncode != 0
    assert not any(call[0] == "diskutil" for call in calls)


@pytest.mark.parametrize("parent", [None, "disk4s1", "/dev/disk4", "disk4 extra"])
def test_parent_device_must_be_a_declared_whole_disk(lifecycle_harness, parent):
    state, run = lifecycle_harness
    volume = {"MountPoint": state["requested_mount"]}
    if parent is not None:
        volume["ParentWholeDisk"] = parent
    result, calls = run('openhcs_detach_disk_image "$mounted_device"', volume=volume)
    assert result.returncode != 0
    assert "Could not resolve the backing device" in result.stderr
    assert not any(call[:2] == ["hdiutil", "detach"] for call in calls)


@pytest.mark.parametrize(
    (
        "normal_status",
        "normal_removes_disk",
        "force_status",
        "force_removes_disk",
        "success",
    ),
    [
        (0, True, 0, True, True),
        (1, True, 0, True, True),
        (1, False, 0, True, True),
        (1, False, 1, True, True),
        (1, False, 1, False, False),
        (1, False, 0, False, False),
        (0, False, 1, False, False),
    ],
)
def test_detach_proves_backing_device_absence(
    lifecycle_harness,
    normal_status,
    normal_removes_disk,
    force_status,
    force_removes_disk,
    success,
):
    _state, run = lifecycle_harness
    result, calls = run(
        'openhcs_detach_disk_image "$mounted_device"',
        normal_status=normal_status,
        normal_removes_disk=normal_removes_disk,
        force_status=force_status,
        force_removes_disk=force_removes_disk,
    )
    assert (result.returncode == 0) is success, result.stderr
    detach_calls = [call for call in calls if call[:2] == ["hdiutil", "detach"]]
    assert detach_calls[0] == ["hdiutil", "detach", "/dev/disk4"]
    assert len(detach_calls) == (1 if normal_removes_disk else 2)
    if not normal_removes_disk:
        assert detach_calls[1] == ["hdiutil", "detach", "-force", "/dev/disk4"]
    if normal_status:
        assert "Resource busy" in result.stderr
    if not success:
        assert "remains attached" in result.stderr
    assert calls[-1] == (
        ["test", "!", "-e", "/dev/disk4"]
        if normal_removes_disk
        else ["test", "-e", "/dev/disk4"]
    )
    assert ["diskutil", "info", "/dev/disk4"] not in calls


@pytest.mark.skipif(
    sys.platform != "darwin", reason="Requires native macOS disk images"
)
def test_native_busy_disk_image_detaches_and_retains_payload(tmp_path: Path):
    """Hold a real file open, release the owned image, then verify its archive."""
    writable = tmp_path / "writable.dmg"
    compressed = tmp_path / "verified.dmg"
    mount = tmp_path / "mount"
    mount.mkdir()
    lifecycle_source = f"source {shlex.quote(str(LIFECYCLE))}; "

    def command(*args):
        return subprocess.run(
            args, check=True, capture_output=True, text=True, timeout=120
        )

    def lifecycle(expression):
        return command(
            "bash", "-c", "set -euo pipefail; " + lifecycle_source + expression
        )

    command("/usr/bin/hdiutil", "create", "-size", "64m", "-fs", "HFS+", str(writable))
    device = ""
    holder = None
    try:
        device = lifecycle(
            f"openhcs_attach_writable_disk_image {shlex.quote(str(writable))} {shlex.quote(str(mount))}"
        ).stdout.strip()
        assert Path(device).exists()
        payload = mount / "payload.txt"
        payload.write_text("OpenHCS disk-image round trip.\n")
        holder = subprocess.Popen(
            [
                sys.executable,
                "-c",
                "import sys; stream=open(sys.argv[1]); print('ready',flush=True); sys.stdin.read()",
                str(payload),
            ],
            cwd=mount,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            text=True,
        )
        assert select.select([holder.stdout], [], [], 10)[
            0
        ], "Image holder did not start"
        assert holder.stdout.readline().strip() == "ready"
        detached = lifecycle(f"openhcs_detach_disk_image {shlex.quote(device)}")
        assert "Releasing the still-attached owned disk image" in detached.stderr
        assert not Path(device).exists()
        device = ""
        holder.communicate(timeout=10)
        holder = None
        command(
            "/usr/bin/hdiutil",
            "convert",
            str(writable),
            "-format",
            "UDZO",
            "-o",
            str(compressed),
        )
        command("/usr/bin/hdiutil", "verify", str(compressed))
        device = lifecycle(
            f"openhcs_attach_readonly_disk_image {shlex.quote(str(compressed))} {shlex.quote(str(mount))}"
        ).stdout.strip()
        assert Path(device).exists()
        assert (mount / "payload.txt").read_text() == "OpenHCS disk-image round trip.\n"
        lifecycle(f"openhcs_detach_disk_image {shlex.quote(device)}")
        assert not Path(device).exists()
        device = ""
    finally:
        if holder is not None:
            holder.kill()
            holder.communicate(timeout=10)
        if device:
            lifecycle(f"openhcs_cleanup_disk_image {shlex.quote(device)}")
