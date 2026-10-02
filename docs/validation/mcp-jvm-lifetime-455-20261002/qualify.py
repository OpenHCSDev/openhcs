"""One fresh public MCP session, with authoritative child exit disposition.

Parent invokes separately for health-only and read-only inventory. No runtime,
viewer, science job, registration, download or uncertain request replay.
"""

import argparse
import json
from pathlib import Path
import sys
import time

import openhcs
from openhcs.mcp.dev_client import McpDevClient


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("evidence", type=Path)
    parser.add_argument("--installed-root", required=True, type=Path)
    parser.add_argument("--plate-path", type=Path)
    args = parser.parse_args()
    assert Path(openhcs.__file__).resolve().is_relative_to(args.installed_root.resolve())
    assert not args.evidence.exists(), "Preserve every earlier attempt."
    args.evidence.mkdir(parents=True)
    with (args.evidence / "requests-replies.jsonl").open("x") as journal, \
         (args.evidence / "mcp-diagnostic.log").open("x+") as diagnostic:
        client = McpDevClient(server_stderr=diagnostic, use_resident_server=False)
        client.start()
        process = client._session.require_process()
        def call(tool, arguments):
            journal.write(json.dumps({"request": {"tool": tool, "arguments": arguments}}) + "\n")
            journal.flush()
            started = time.monotonic()
            result = client.execute(
                ("call", tool, "--arguments", json.dumps(arguments), "--json"),
                timeout_seconds=10,
            )
            journal.write(json.dumps({"response": result.payload, "returncode": result.returncode,
                                      "elapsed_seconds": time.monotonic() - started}) + "\n")
            journal.flush()
            assert result.returncode == 0, result.rendered_output
            return result
        try:
            call("openhcs_health_check", {})
            if args.plate_path is not None:
                call("openhcs_query_plate_files", {
                    "plate_path": str(args.plate_path.resolve()), "microscope_type": "bioformats",
                    "kind": "image", "include_previews": False, "limit": 1,
                })
                call("openhcs_health_check", {})
        finally:
            started = time.monotonic()
            client.close()
            disposition = {"mcp_child_pid": process.pid, "mcp_child_returncode": process.returncode,
                           "close_elapsed_seconds": time.monotonic() - started,
                           "ordinary_call_idle_seconds": 10}
            journal.write(json.dumps({"child_exit": disposition}) + "\n")
            journal.flush()
            diagnostic.seek(0)
            stderr = diagnostic.read()
            print(json.dumps(disposition), flush=True)
            assert process.returncode == 0, stderr
            assert "Fatal error in exception handling" not in stderr, stderr


if __name__ == "__main__":
    main()
