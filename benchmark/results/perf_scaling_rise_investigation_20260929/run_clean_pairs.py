import csv
import hashlib
import json
import os
import subprocess
import sys
import threading
import time
from pathlib import Path


def monitor(proc, dest):
    ticks = os.sysconf("SC_CLK_TCK")
    with dest.open("w") as f:
        while proc.poll() is None:
            processes = []
            for stat_path in Path("/proc").glob("[0-9]*/stat"):
                try:
                    raw = stat_path.read_text()
                    comm = raw[raw.index("(") + 1 : raw.rindex(")")]
                    v = raw[raw.rindex(")") + 2 :].split()
                    processes.append(
                        {
                            "pid": int(stat_path.parent.name),
                            "comm": comm,
                            "state": v[0],
                            "ppid": int(v[1]),
                            "utime": int(v[11]) / ticks,
                            "stime": int(v[12]) / ticks,
                            "threads": int(v[17]),
                            "start_ticks": int(v[19]),
                            "rss_pages": int(v[21]),
                            "cpu": int(v[36]),
                            "delay_ticks": int(v[39]),
                        }
                    )
                except (FileNotFoundError, ProcessLookupError, PermissionError):
                    pass
            descendants = {proc.pid}
            changed = True
            while changed:
                new = descendants | {
                    p["pid"] for p in processes if p["ppid"] in descendants
                }
                changed = new != descendants
                descendants = new
            frequencies = {
                p.parent.parent.name: p.read_text().strip()
                for p in Path("/sys/devices/system/cpu").glob(
                    "cpu[0-9]*/cpufreq/scaling_cur_freq"
                )
            }
            f.write(
                json.dumps(
                    {
                        "time": time.time(),
                        "load": os.getloadavg(),
                        "frequencies_khz": frequencies,
                        "processes": [
                            p
                            for p in processes
                            if p["pid"] in descendants
                            or p["comm"]
                            in ("x0vncserver", "kodi.bin", "codex", "opencode")
                        ],
                    }
                )
                + "\n"
            )
            f.flush()
            time.sleep(1)


def main():
    root = Path(__file__).resolve().parents[3]
    runs = root.parent / "openhcs-benchmark-runs"
    path = root / "openhcs/processing/backends/cellprofiler/texture.py"
    candidate = path.read_bytes()
    baseline = subprocess.check_output(
        [
            "git",
            "show",
            "5976f8547:openhcs/processing/backends/cellprofiler/texture.py",
        ],
        cwd=root,
    )
    evidence = runs / "perf-scaling-rise-investigation-20260929"
    evidence.mkdir(exist_ok=True)
    (evidence / "fused_texture.py").write_bytes(candidate)
    (evidence / "control_texture.py").write_bytes(baseline)
    env = os.environ.copy()
    env.update(
        OPENHCS_CPU_ONLY="true",
        OPENHCS_SUBPROCESS_NO_GPU="1",
        POLYSTORE_SUBPROCESS_NO_GPU="1",
        NUMBA_CACHE_DIR="/tmp/openhcs-registry-kernel-prewarm-production-20260929-c2",
    )
    for name in (
        "OPENHCS_WORKER_PROFILE_DIR",
        "NUMBA_ENABLE_SYS_MONITORING",
        "OPENHCS_PROFILE_FUNCTION_RUNTIME",
    ):
        env.pop(name, None)
    (evidence / "scope.json").write_text(
        json.dumps(
            {
                "head": subprocess.check_output(
                    ["git", "rev-parse", "HEAD"], cwd=root, text=True
                ).strip(),
                "texture_hashes": {
                    "fused": hashlib.sha256(candidate).hexdigest(),
                    "control": hashlib.sha256(baseline).hexdigest(),
                },
                "env": {
                    k: v
                    for k, v in env.items()
                    if k.startswith(
                        ("OPENHCS", "NUMBA", "OMP", "MKL", "OPENBLAS", "POLYSTORE")
                    )
                },
                "design": "control/fused/fused/control; current main/dependencies; existing family warm before each fresh server; no other agent CPU work; repeated byte-identical source images",
            },
            indent=2,
        )
        + "\n"
    )
    try:
        for variant, number in [
            ("control", 1),
            ("fused", 1),
            ("fused", 2),
            ("control", 2),
        ]:
            path.write_bytes(candidate if variant == "fused" else baseline)
            warming = "from openhcs.processing.backends.cellprofiler.texture import HaralickTextureBackendStrategy,ObjectTextureCropBackendStrategy; HaralickTextureBackendStrategy.prepare_registered_family(); ObjectTextureCropBackendStrategy.prepare_registered_family()"
            started = time.perf_counter()
            with (evidence / f"{variant}_{number}_warm.log").open("w") as log:
                subprocess.run(
                    [sys.executable, "-c", warming],
                    cwd=root,
                    env=env,
                    stdout=log,
                    stderr=subprocess.STDOUT,
                    timeout=90,
                    check=True,
                )
            warming_seconds = time.perf_counter() - started
            out = runs / f"perf-rise-{variant}-16w-r{number}-20260929"
            with out.with_suffix(".log").open("w") as log:
                proc = subprocess.Popen(
                    [
                        sys.executable,
                        "scripts/benchmark_cppipe_well_throughput.py",
                        "--manifest",
                        "benchmark/manifests/official30_portable_axis1.json",
                        "--output-dir",
                        str(out),
                        "--mode",
                        "16w_4c",
                        "--case",
                        "ExampleImagingFlowCytometryObjectsInGrid",
                    ],
                    cwd=root,
                    env=env,
                    stdout=log,
                    stderr=subprocess.STDOUT,
                )
                watcher = threading.Thread(
                    target=monitor,
                    args=(proc, evidence / f"{variant}_{number}_resources.jsonl"),
                )
                watcher.start()
                code = proc.wait(timeout=300)
                watcher.join()
                assert code == 0, code
            with (out / "well_throughput.csv").open() as stream:
                row = next(csv.DictReader(stream))
            result = {
                "variant": variant,
                "repetition": number,
                "warming_seconds": warming_seconds,
                "compile": float(row["compile_seconds"]),
                "execution": float(row["execute_seconds"]),
                "total": float(row["total_seconds"]),
                "status": row["status"],
                "output_dir": str(out),
            }
            with (evidence / "observations.jsonl").open("a") as f:
                f.write(json.dumps(result) + "\n")
            print(json.dumps(result), flush=True)
    finally:
        path.write_bytes(candidate)


if __name__ == "__main__":
    main()
