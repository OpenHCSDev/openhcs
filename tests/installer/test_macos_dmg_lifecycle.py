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
        can_release = mode == "normal" or not state["volumes_mounted"]
        if state[mode + "_removes_disk"] and can_release:
            state["attached"] = False
        state_path.write_text(json.dumps(state))
        if state[mode + "_status"]:
            print("hdiutil: couldn't eject disk4 - Resource busy", file=sys.stderr)
        raise SystemExit(state[mode + "_status"])
elif tool == "diskutil":
    if args == ["unmountDisk", "force", "/dev/disk4"]:
        if state["unmount_releases_volumes"]:
            state["volumes_mounted"] = False
        state_path.write_text(json.dumps(state))
        print("Owned volume unmount diagnostic", file=sys.stderr)
        raise SystemExit(state["unmount_status"])
    elif args == ["list", "-plist", "/dev/disk4"]:
        emit({"AllDisks": state["family"]})
    elif args[:2] == ["info", "-plist"] and args[-1].startswith("/dev/"):
        member = args[-1].removeprefix("/dev/")
        emit({"DeviceIdentifier": member, "ParentWholeDisk": state["parents"][member]})
    elif args[:2] == ["info", "-plist"]:
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
elif tool == "sudo":
    assert args[:4] == ["-n", "/usr/sbin/lsof", "-nP", "--"]
    print("Owned device holder diagnostic", file=sys.stderr)
    raise SystemExit(state["holder_status"])
elif tool == "log":
    assert args[:7] == ["show", "--last", "2m", "--style", "compact", "--info", "--debug"]
    assert args[7] == "--predicate"
    assert args[8] == "process == 'diskarbitrationd' AND eventMessage MATCHES '.*\\\\bdisk4(s[0-9]+)*\\\\b.*'"
    print("Owned Disk Arbitration failure diagnostic", file=sys.stderr)
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
        "volumes_mounted": True,
        "unmount_status": 0,
        "unmount_releases_volumes": True,
        "attach_status": 0,
        "normal_status": 0,
        "normal_removes_disk": True,
        "force_status": 0,
        "force_removes_disk": True,
        "family": ["disk4", "disk4s1"],
        "parents": {"disk4": "disk4", "disk4s1": "disk4"},
        "holder_status": 1,
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
                ("/usr/bin/sudo", "sudo"),
                ("/usr/bin/log", "log"),
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
        assert detach_calls[1] == [
            "hdiutil",
            "detach",
            "-debug",
            "-force",
            "/dev/disk4",
        ]
        unmount = ["diskutil", "unmountDisk", "force", "/dev/disk4"]
        assert calls.count(unmount) == 1
        assert calls.index(unmount) < calls.index(detach_calls[1])
        assert "Owned device holder diagnostic" in result.stderr
        assert "Owned volume unmount diagnostic" in result.stderr
    if normal_status:
        assert "Resource busy" in result.stderr
    if not success:
        assert "remains attached" in result.stderr
    terminal_check = (
        ["test", "!", "-e", "/dev/disk4"]
        if normal_removes_disk
        else ["test", "-e", "/dev/disk4"]
    )
    assert terminal_check in calls
    assert any(call[0] == "log" for call in calls) is (not success)
    if not success:
        assert "Owned Disk Arbitration failure diagnostic" in result.stderr
    assert ["diskutil", "info", "/dev/disk4"] not in calls


@pytest.mark.parametrize("family", [["disk4", "disk4s1"], ["disk4s1", "disk4"]])
def test_holder_probe_covers_declared_raw_and_block_device_family(
    lifecycle_harness, family
):
    _state, run = lifecycle_harness
    result, calls = run(
        'openhcs_detach_disk_image "$mounted_device"',
        normal_removes_disk=False,
        family=family,
    )
    assert result.returncode == 0, result.stderr
    holder_calls = [call for call in calls if call[0] == "sudo"]
    assert holder_calls == [
        [
            "sudo",
            "-n",
            "/usr/sbin/lsof",
            "-nP",
            "--",
            *(
                path
                for member in family
                for path in (f"/dev/{member}", f"/dev/r{member}")
            ),
        ]
    ]


@pytest.mark.parametrize(
    ("family", "parents"),
    [
        (["disk4", "disk0s1"], {"disk4": "disk4", "disk0s1": "disk0"}),
        (["disk4", "../../somewhere"], {"disk4": "disk4"}),
        ([], {}),
    ],
)
def test_holder_probe_does_not_expand_to_unvalidated_devices(
    lifecycle_harness, family, parents
):
    _state, run = lifecycle_harness
    result, calls = run(
        'openhcs_detach_disk_image "$mounted_device"',
        normal_removes_disk=False,
        family=family,
        parents={"disk4": "disk4", **parents},
    )
    assert result.returncode == 0, result.stderr
    assert not any(call[0] == "sudo" for call in calls)
    assert all(
        call[-1] == "/dev/disk4" for call in calls if call[:2] == ["hdiutil", "detach"]
    )


def test_unavailable_privileged_diagnostics_do_not_change_detach_outcome(
    lifecycle_harness,
):
    _state, run = lifecycle_harness
    result, calls = run(
        'openhcs_detach_disk_image "$mounted_device"',
        normal_removes_disk=False,
        holder_status=77,
    )
    assert result.returncode == 0, result.stderr
    assert len([call for call in calls if call[:2] == ["hdiutil", "detach"]]) == 2


@pytest.mark.parametrize(
    ("unmount_status", "unmount_releases_volumes", "success"),
    [(0, True, True), (1, False, False), (0, False, False)],
)
def test_forced_detach_follows_explicit_volume_release(
    lifecycle_harness, unmount_status, unmount_releases_volumes, success
):
    _state, run = lifecycle_harness
    result, calls = run(
        'openhcs_detach_disk_image "$mounted_device"',
        normal_status=1,
        normal_removes_disk=False,
        unmount_status=unmount_status,
        unmount_releases_volumes=unmount_releases_volumes,
    )
    assert (result.returncode == 0) is success, result.stderr
    assert calls.count(["diskutil", "unmountDisk", "force", "/dev/disk4"]) == 1
    assert "Owned volume unmount diagnostic" in result.stderr
    if not success:
        assert "Owned disk image remains attached" in result.stderr


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

    def command(*args, check=True):
        result = subprocess.run(
            args, check=False, capture_output=True, text=True, timeout=120
        )
        if check:
            assert result.returncode == 0, (
                f"Command {args!r} exited {result.returncode}\n"
                f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
            )
        return result

    def lifecycle(expression, *, check=True):
        return command(
            "bash",
            "-c",
            "set -euo pipefail; " + lifecycle_source + expression,
            check=check,
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
        # A root-owned raw-device handle must be visible even though the block
        # device alone does not identify it. Inspect without changing the image.
        with subprocess.Popen(
            [
                "/usr/bin/sudo",
                "-n",
                sys.executable,
                "-c",
                "import os,signal,sys; signal.alarm(30); stream=open(sys.argv[1],'rb'); "
                "print(os.getpid(),flush=True); sys.stdin.read()",
                str(Path(device).with_name("r" + Path(device).name)),
            ],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            text=True,
        ) as raw_holder:
            try:
                assert select.select([raw_holder.stdout], [], [], 10)[0]
                holder_pid = int(raw_holder.stdout.readline().strip())
                diagnostics = lifecycle(
                    f"_openhcs_disk_image_holders {shlex.quote(device)}",
                    check=False,
                )
                # Known-holder output is the proof; not every probed family
                # member needs to have an open handle.
                assert str(holder_pid) in diagnostics.stderr.split(), (
                    f"Holder PID {holder_pid} absent; diagnostic exited {diagnostics.returncode}\n"
                    f"stdout:\n{diagnostics.stdout}\nstderr:\n{diagnostics.stderr}"
                )
            finally:
                raw_holder.communicate(timeout=10)
        lifecycle(f"openhcs_detach_disk_image {shlex.quote(device)}")
        assert not Path(device).exists()
        device = ""
    finally:
        if holder is not None:
            holder.kill()
            holder.communicate(timeout=10)
        if device:
            lifecycle(f"openhcs_cleanup_disk_image {shlex.quote(device)}")
