"""TEMPORARY (surface R1): time cold function-catalog preparation phase by phase.

Wall time per status row, CPU time of this process and its finished children,
and (R1_NUMBA_EVENTS=1) the self time of every Numba compilation.
"""

import collections
import json
import os
import platform
import sys
import time

START = time.perf_counter()
rows = []


def cpu_seconds():
    t = os.times()
    return t.user + t.system + t.children_user + t.children_system


def status(message):
    rows.append((time.perf_counter() - START, cpu_seconds(), str(message)))


def numba_compile_report(listener):
    stack = []
    self_time = collections.Counter()
    count = collections.Counter()
    for timestamp, event in listener.buffer:
        function = event.data["dispatcher"].py_func
        name = f"{getattr(function, '__module__', '?')}.{getattr(function, '__qualname__', '?')}"
        if event.is_start:
            stack.append([name, timestamp, 0.0])
        elif stack:
            started_name, started, child = stack.pop()
            total = timestamp - started
            self_time[started_name] += total - child
            count[started_name] += 1
            if stack:
                stack[-1][2] += total
    total = sum(self_time.values())
    print(f"NUMBA compile self time {total:.1f}s over {sum(count.values())} compilations of {len(count)} functions")
    by_module = collections.Counter()
    for name, seconds in self_time.items():
        by_module[name.split(".<locals>")[0].rsplit(".", 1)[0]] += seconds
    print("-- by module")
    for module, seconds in by_module.most_common(25):
        print(f"{seconds:8.2f}s  {module}")
    print("-- by function (signatures compiled)")
    for name, seconds in self_time.most_common(40):
        print(f"{seconds:8.2f}s  x{count[name]:<3d} {name}")


def main():
    out = sys.argv[1]
    print("platform", platform.platform(), platform.machine(), "cpus", os.cpu_count())
    print("NUMBA_CACHE_DIR", os.environ.get("NUMBA_CACHE_DIR"), "OPENHCS_CPU_ONLY", os.environ.get("OPENHCS_CPU_ONLY"))
    status("process started")
    from openhcs.processing.backends.lib_registry.registry_service import RegistryService

    status("registry service imported")
    if os.environ.get("R1_NO_CHILDREN"):
        from openhcs.core.processing_preparation import PreparationCacheBatch

        PreparationCacheBatch.populate_child_caches = lambda *args, **kwargs: None
    listener = None
    if os.environ.get("R1_NUMBA_EVENTS"):
        from numba.core import event

        listener = event.RecordingListener()
        event.register("numba:compile", listener)
    if os.environ.get("R1_PROFILE"):
        import cProfile
        import pstats

        profile = cProfile.Profile()
        profile.runcall(RegistryService.prepare_in_current_process, status_callback=status)
        pstats.Stats(profile).sort_stats("cumulative").print_stats(70)
    else:
        RegistryService.prepare_in_current_process(status_callback=status)
    status("prepared")
    with open(out, "w", encoding="utf-8") as handle:
        for wall, cpu, message in rows:
            handle.write(json.dumps({"t": wall, "cpu": cpu, "message": message}) + "\n")
    gaps = sorted(
        ((b[0] - a[0], b[1] - a[1], a[2], b[2]) for a, b in zip(rows, rows[1:])), reverse=True
    )
    print(f"TOTAL wall {rows[-1][0]:.1f}s cpu {rows[-1][1]:.1f}s over {len(rows)} status rows")
    for wall, cpu, before, after in gaps[:30]:
        print(f"wall {wall:7.2f}s cpu {cpu:7.2f}s  {before[:100]}  ->  {after[:100]}")
    if listener is not None:
        numba_compile_report(listener)


if __name__ == "__main__":
    main()
