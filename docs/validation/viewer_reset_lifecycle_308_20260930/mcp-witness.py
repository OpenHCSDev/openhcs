"""Mechanical receipt capture through the existing persistent MCP client."""

import json
import sys
from pathlib import Path

from openhcs.mcp.dev_client import McpDevClient

receipts = Path(sys.argv[1])
receipts.mkdir(parents=True, exist_ok=False)
with (receipts / "mcp-stderr.log").open("x") as stderr:
    with McpDevClient(server_stderr=stderr, use_resident_server=False) as client:
        print("MCP client initialized", flush=True)
        for index, line in enumerate(sys.stdin, start=1):
            argv = json.loads(line)
            if argv == ["exit"]:
                break
            (receipts / f"request-{index:03d}.json").write_text(line)
            try:
                result = client.execute(argv)
            except SystemExit as error:
                receipt = {
                    "argv": argv,
                    "client_usage_exit": error.code,
                }
            else:
                receipt = {
                    "argv": result.argv,
                    "returncode": result.returncode,
                    "payload": result.payload,
                    "server_stderr_tail": result.server_stderr_tail,
                }
            with (receipts / f"receipt-{index:03d}.json").open("x") as destination:
                json.dump(receipt, destination, indent=2)
            print(json.dumps(receipt), flush=True)
