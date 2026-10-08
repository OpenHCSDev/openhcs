"""Bounded closure-owner checks; no provider, MCP, scope or native launch."""

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

import psutil


class ControllerClosureTests(unittest.TestCase):
    def setUp(self):
        scratch = Path("/home/ts/.cache/agent-scratch")
        scratch.mkdir(parents=True, exist_ok=True)
        self.directory = tempfile.TemporaryDirectory(prefix="controller-closure-", dir=scratch)
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.runtime = self.root / "A/author-workspace/output/runtime"
        self.runtime.mkdir(parents=True)
        (self.runtime / "first-mcp-started.epoch").write_text("1\n")
        self.author = self.runtime / "author-events.typescript"
        self.author.write_text('{"type":"thread.started","thread_id":"original-thread"}\n')
        for name in ("mcp.stdin", "mcp.stdout"):
            (self.runtime / name).write_text('Script done on controlled fixture [COMMAND_EXIT_CODE="0"]\n')
        absent = []
        for pid in range(10000000, 10000010):
            if not psutil.pid_exists(pid):
                absent.append(pid)
            if len(absent) == 2:
                break
        self.launch = {
            "slot": "A", "original_tool_handle": 27800,
            "author_pid": absent[0], "bwrap_pid": absent[1],
            "author_invocation": "a" * 32, "thread_id": "original-thread",
            "original_launch_terminal_observation": {
                "tool_handle": 27800, "exit_code": 143,
                "author_pid_absent": absent[0], "bwrap_pid_absent": absent[1],
                "author_scope_absent": True,
            },
            "interruption_custody": {
                "receipt": "INTERRUPTION-CUSTODY.json",
                "file_manifest": "INTERRUPTION-CUSTODY-FILES.json",
            },
        }
        self.interruption = {
            "file_manifest": "INTERRUPTION-CUSTODY-FILES.json",
            "original_author_termination": {"tool_handle": 27800, "exit_code": 143},
        }
        self.manifest = {"files": []}
        for name in ("author-events.typescript", "mcp.stdin", "mcp.stdout"):
            path = self.runtime / name
            content = path.read_bytes()
            self.manifest["files"].append({
                "path": str(path), "bytes": len(content),
                "sha256": hashlib.sha256(content).hexdigest(),
            })
        repo = Path(__file__).resolve().parents[2]
        source = (repo / "scripts/blind_analysis/operations/slot-env.sh").read_text()
        self.owner = re.search(r"(?ms)^fleet_require_closed_controllers\(\) \{\n.*?^}\n", source).group()

    def invoke(self, *, state="inactive", invocation="", load_state="not-found", controllers="", systemctl_status=0,
               list_status=0, predecessor=None, fuser_status=None):
        for name, value in (
            ("AUTHOR-LAUNCH-CUSTODY.json", self.launch),
            ("INTERRUPTION-CUSTODY.json", self.interruption),
            ("INTERRUPTION-CUSTODY-FILES.json", self.manifest),
        ):
            (self.root / name).write_text(json.dumps(value))
        env = dict(os.environ, FLEET_PYTHON=sys.executable, FLEET_RUN_ROOT=str(self.root),
                   FLEET_SLOT="A", FLEET_WORKSPACE=str(self.runtime.parent.parent),
                   FLEET_UNIT="controlled-a", FLEET_PREDECESSOR_AUTHOR_UNIT="controlled-a-author",
                   FLEET_AUTHOR_UNIT="controlled-a-author-new", FLEET_CLIENT_UNIT="controlled-a-mcp-new",
                   FLEET_PREDECESSOR_RECORD_RUNTIME=str(predecessor or self.runtime),
                   TEST_STATE=state, TEST_INVOCATION=invocation, TEST_LOAD_STATE=load_state, TEST_CONTROLLERS=controllers,
                   TEST_SYSTEMCTL_STATUS=str(systemctl_status), TEST_LIST_STATUS=str(list_status))
        boundary = """
systemctl() {
  if [[ "$2" == list-units ]]; then
    printf '%s' "$TEST_CONTROLLERS"
    return "$TEST_LIST_STATUS"
  fi
  [[ "$TEST_SYSTEMCTL_STATUS" == 0 ]] || return "$TEST_SYSTEMCTL_STATUS"
  case "$5" in
    ActiveState) printf '%s\\n' "$TEST_STATE" ;;
    InvocationID) printf '%s\\n' "$TEST_INVOCATION" ;;
    LoadState) printf '%s\\n' "$TEST_LOAD_STATE" ;;
    *) return 64 ;;
  esac
}
"""
        if fuser_status is not None:
            boundary += f"fuser() {{ return {fuser_status}; }}\n"
        # A conditional caller disables Bash errexit throughout the function.
        # The owner must propagate every refusal explicitly, not rely on -e.
        return subprocess.run(
            ["bash", "-s"], input="set -euo pipefail\n" + self.owner + boundary +
            "if fleet_require_closed_controllers; then exit 0; else exit $?; fi\n",
            env=env, text=True, capture_output=True, timeout=10,
        )

    def test_positive_interruption_preserves_journals(self):
        before = {path: path.read_bytes() for path in self.runtime.iterdir()}
        result = self.invoke()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(before, {path: path.read_bytes() for path in self.runtime.iterdir()})
        self.assertEqual(self.invoke(invocation="a" * 32, state="failed").returncode, 0)

    def test_normal_footer_does_not_need_interruption_custody(self):
        self.author.write_text('Script done on controlled fixture [COMMAND_EXIT_CODE="42"]\n')
        self.launch = None
        self.interruption = None
        self.manifest = None
        self.assertEqual(self.invoke().returncode, 0)

    def test_terminal_observation_must_be_known_and_same_launch(self):
        terminal = self.launch["original_launch_terminal_observation"]
        for exit_code in (None, "UNKNOWN", 0, 42, 128, 193, True):
            with self.subTest(exit_code=exit_code):
                terminal["exit_code"] = exit_code
                self.assertNotEqual(self.invoke().returncode, 0)
        terminal["exit_code"] = 143
        for key, value in (("tool_handle", 99), ("author_pid_absent", 99),
                           ("bwrap_pid_absent", 99), ("author_scope_absent", False)):
            with self.subTest(key=key):
                old = terminal[key]
                terminal[key] = value
                self.assertNotEqual(self.invoke().returncode, 0)
                terminal[key] = old
        self.interruption["original_author_termination"]["exit_code"] = 137
        self.assertNotEqual(self.invoke().returncode, 0)

    def test_live_controller_pids_are_refused(self):
        for role in ("author", "bwrap"):
            with self.subTest(role=role):
                old = self.launch[f"{role}_pid"]
                self.launch[f"{role}_pid"] = os.getpid()
                self.launch["original_launch_terminal_observation"][f"{role}_pid_absent"] = os.getpid()
                self.assertNotEqual(self.invoke().returncode, 0)
                self.launch[f"{role}_pid"] = old
                self.launch["original_launch_terminal_observation"][f"{role}_pid_absent"] = old

    def test_scope_and_borrower_uncertainty_are_refused(self):
        for kwargs in (
            {"state": "active"}, {"state": "activating"}, {"state": ""},
            {"invocation": "b" * 32}, {"systemctl_status": 1}, {"list_status": 1},
            {"load_state": "loaded"}, {"load_state": ""},
            {"controllers": "controlled-a-mcp-old.scope loaded active running"},
            {"fuser_status": 2},
        ):
            with self.subTest(kwargs=kwargs):
                self.assertNotEqual(self.invoke(**kwargs).returncode, 0)
        with self.author.open("rb"):
            self.assertEqual(self.invoke().returncode, 75)

    def test_original_custody_cannot_close_a_recovery_predecessor(self):
        predecessor = self.runtime / "old-recovery"
        predecessor.mkdir()
        for name in ("author-events.typescript", "mcp.stdin", "mcp.stdout"):
            (predecessor / name).write_bytes((self.runtime / name).read_bytes())
        self.assertNotEqual(self.invoke(predecessor=predecessor).returncode, 0)

    def test_changed_missing_or_ambiguous_journal_custody_is_refused(self):
        for index, entry in enumerate(self.manifest["files"]):
            with self.subTest(journal=entry["path"]):
                old = entry["sha256"]
                entry["sha256"] = "0" * 64
                self.assertNotEqual(self.invoke().returncode, 0)
                entry["sha256"] = old
                self.manifest["files"].append(entry)
                self.assertNotEqual(self.invoke().returncode, 0)
                self.manifest["files"].pop()
                self.manifest["files"].pop(index)
                self.assertNotEqual(self.invoke().returncode, 0)
                self.manifest["files"].insert(index, entry)
        for key, value in (("slot", "OTHER"), ("thread_id", "other-thread")):
            old = self.launch[key]
            self.launch[key] = value
            self.assertNotEqual(self.invoke().returncode, 0)
            self.launch[key] = old
        del self.launch["original_launch_terminal_observation"]
        self.assertNotEqual(self.invoke().returncode, 0)

    def test_mcp_footers_and_first_start_remain_required(self):
        for name in ("mcp.stdin", "mcp.stdout", "first-mcp-started.epoch"):
            with self.subTest(name=name):
                path = self.runtime / name
                old = path.read_bytes()
                path.unlink()
                self.assertNotEqual(self.invoke().returncode, 0)
                path.write_bytes(old)


if __name__ == "__main__":
    unittest.main()
