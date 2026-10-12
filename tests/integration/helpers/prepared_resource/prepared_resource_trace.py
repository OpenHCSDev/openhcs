"""Append one line per event of the guard's custom functions and its driver.

On ``PYTHONPATH`` of the driver, the execution server and its workers, so a
custom-function source (which may not import ``os``) can record which process
prepared, loaded or called it.
"""

import json
import os
import time

TRACE_VARIABLE = "OPENHCS_PREPARED_RESOURCE_TRACE"


def record(kind: str, function: str = "", **facts: object) -> None:
    with open(os.environ[TRACE_VARIABLE], "a", encoding="utf-8") as stream:
        stream.write(
            json.dumps(
                {
                    "kind": kind,
                    "function": function,
                    "pid": os.getpid(),
                    "parent": os.getppid(),
                    "time": time.time(),
                    **facts,
                }
            )
            + "\n"
        )
