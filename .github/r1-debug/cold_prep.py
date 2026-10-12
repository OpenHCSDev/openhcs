"""TEMPORARY (surface R1): time cold function-catalog preparation phase by phase."""

import json
import os
import platform
import sys
import time

START = time.perf_counter()
rows = []


def status(message):
    now = time.perf_counter() - START
    rows.append((now, str(message)))


def main():
    out = sys.argv[1]
    print("platform", platform.platform(), platform.machine(), "cpus", os.cpu_count())
    print("NUMBA_CACHE_DIR", os.environ.get("NUMBA_CACHE_DIR"), "OPENHCS_CPU_ONLY", os.environ.get("OPENHCS_CPU_ONLY"))
    status("process started")
    from openhcs.processing.backends.lib_registry.registry_service import RegistryService

    status("registry service imported")
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
        for at, message in rows:
            handle.write(json.dumps({"t": at, "message": message}) + "\n")
    gaps = sorted(
        ((b[0] - a[0], a[1], b[1]) for a, b in zip(rows, rows[1:])), reverse=True
    )
    print(f"TOTAL {rows[-1][0]:.1f}s over {len(rows)} status rows")
    for gap, before, after in gaps[:30]:
        print(f"{gap:8.2f}s  {before[:110]}  ->  {after[:110]}")
    heavy = sorted(name for name in sys.modules if name.split(".")[0] in {"torch", "jax", "tensorflow", "cupy", "basicpy", "skimage", "numba", "scipy", "napari", "PyQt6"} and "." not in name)
    print("top-level heavy modules loaded:", heavy)


if __name__ == "__main__":
    main()
