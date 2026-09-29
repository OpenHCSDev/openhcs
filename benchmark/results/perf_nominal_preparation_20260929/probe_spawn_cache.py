"""Observe dispatcher cache hits in genuinely fresh spawned interpreters."""

import json
import multiprocessing
import os
import sys
import time
from pathlib import Path

sys.path.insert(0, "/home/ts/code/projects/openhcs-compile-perf")


def prepare(queue):
    from numba import config
    from numba.core.registry import CPUDispatcher

    from openhcs.processing.backends.cellprofiler.intensity import (
        ObjectIntensityBackendStrategy,
    )
    from openhcs.processing.backends.cellprofiler.shape import (
        ShapeMeasurementBackendStrategy,
    )

    started = time.perf_counter()
    ObjectIntensityBackendStrategy.prepare_registered_family()
    ShapeMeasurementBackendStrategy.prepare_registered_family()
    preparation_seconds = time.perf_counter() - started
    dispatchers = {}
    for name, module in tuple(sys.modules.items()):
        if module is None or not name.startswith("openhcs."):
            continue
        for value in vars(module).values():
            if isinstance(value, CPUDispatcher):
                dispatchers[id(value)] = value
    stats = [
        {
            "callable": f"{dispatcher.py_func.__module__}.{dispatcher.py_func.__qualname__}",
            "cache_hits": sum(dispatcher.stats.cache_hits.values()),
            "cache_misses": sum(dispatcher.stats.cache_misses.values()),
        }
        for dispatcher in dispatchers.values()
        if dispatcher.signatures
    ]
    queue.put(
        {
            "pid": os.getpid(),
            "parent_pid": os.getppid(),
            "cache_directory": config.CACHE_DIR,
            "preparation_seconds": preparation_seconds,
            "cache_hits": sum(row["cache_hits"] for row in stats),
            "cache_misses": sum(row["cache_misses"] for row in stats),
            "dispatchers": stats,
        }
    )


if __name__ == "__main__":
    context = multiprocessing.get_context("spawn")
    queue = context.SimpleQueue()
    children = [context.Process(target=prepare, args=(queue,)) for _ in range(2)]
    started = time.perf_counter()
    for child in children:
        child.start()
    rows = [queue.get() for child in children]
    for child in children:
        child.join()
        if child.exitcode != 0:
            raise RuntimeError(f"spawned preparation exited {child.exitcode}")
    queue.close()
    elapsed = time.perf_counter() - started
    assert len({row["pid"] for row in rows}) == 2
    assert all(row["cache_hits"] > 0 and row["cache_misses"] == 0 for row in rows), rows
    destination = Path(
        "/home/ts/code/projects/openhcs-benchmark-runs/perf-shared-kernel-cache-spawn-dispatcher-hits-20260929.json"
    )
    destination.write_text(
        json.dumps(
            {
                "start_method": "spawn",
                "parent_pid": os.getpid(),
                "total_seconds": elapsed,
                "workers": rows,
            },
            indent=2,
        )
        + "\n"
    )
    print(destination)
    print(
        json.dumps(
            {
                "total_seconds": elapsed,
                "workers": [
                    {key: value for key, value in row.items() if key != "dispatchers"}
                    for row in rows
                ],
            }
        )
    )
