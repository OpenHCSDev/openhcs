"""Record native MCP authoring evidence from an explicitly isolated GUI bridge.

Commands are the public dev-client argv, not desktop coordinates. The complete
response is retained so rendered figures can be checked against actual UI state.
"""

import argparse
import json
from pathlib import Path

from openhcs.mcp.dev_client import McpDevClient


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipt", type=Path)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    with McpDevClient() as client:
        result = client.execute(args.command, timeout_seconds=30)
    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    args.receipt.write_text(json.dumps({"argv": result.argv, "response": result.payload}, indent=2) + "\n")
    print(result.rendered_output)
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
