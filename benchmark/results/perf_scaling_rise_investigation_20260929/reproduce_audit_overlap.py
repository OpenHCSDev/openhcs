import ast
import csv
import json
import os
import subprocess
import sys
import threading
import time
from pathlib import Path
from types import SimpleNamespace

from run_clean_pairs import monitor

root = Path(__file__).resolve().parents[3]
runs = root.parent / "openhcs-benchmark-runs"
evidence = runs / "perf-scaling-rise-investigation-20260929"


# Capture memory pressure alongside process CPU/RSS without profiling execution.
def pressure(stop, path):
    with path.open("w") as stream:
        while not stop.is_set():
            mem = {
                line.split(":")[0]: line.split(":")[1].strip()
                for line in Path("/proc/meminfo").read_text().splitlines()
                if line.split(":")[0]
                in ("MemAvailable", "SwapFree", "SwapCached", "Dirty")
            }
            stream.write(
                json.dumps(
                    {
                        "time": time.time(),
                        "memory": mem,
                        "memory_psi": Path("/proc/pressure/memory").read_text(),
                        "io_psi": Path("/proc/pressure/io").read_text(),
                        "cpu_psi": Path("/proc/pressure/cpu").read_text(),
                    }
                )
                + "\n"
            )
            stream.flush()
            stop.wait(1)


def run():
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
    # Prior source-alternating driver must finish and restore the candidate first.
    assert (
        root / "openhcs/processing/backends/cellprofiler/texture.py"
    ).read_bytes() == (evidence / "fused_texture.py").read_bytes()
    warm = "from openhcs.processing.backends.cellprofiler.texture import HaralickTextureBackendStrategy,ObjectTextureCropBackendStrategy; HaralickTextureBackendStrategy.prepare_registered_family(); ObjectTextureCropBackendStrategy.prepare_registered_family()"
    with (evidence / "audit_overlap_warm.log").open("w") as log:
        subprocess.run(
            [sys.executable, "-c", warm],
            cwd=root,
            env=env,
            stdout=log,
            stderr=subprocess.STDOUT,
            check=True,
            timeout=90,
        )
    out = runs / "perf-rise-fused-audit-overlap-16w-20260929"
    audits = []
    stopped = threading.Event()
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
        resources = threading.Thread(
            target=monitor,
            args=(
                SimpleNamespace(pid=os.getpid(), poll=proc.poll),
                evidence / "audit_overlap_resources.jsonl",
            ),
        )
        resources.start()
        mem = threading.Thread(
            target=pressure, args=(stopped, evidence / "audit_overlap_pressure.jsonl")
        )
        mem.start()
        try:
            # Main execution begins immediately after the pool's four workers appear.
            observed = None
            while observed is None and proc.poll() is None:
                time.sleep(0.25)
                lines = (
                    (evidence / "audit_overlap_resources.jsonl")
                    .read_text()
                    .splitlines()
                )
                if lines:
                    sample = json.loads(lines[-1])
                    parents = {}
                    for p in sample["processes"]:
                        if p["comm"] == "python":
                            parents.setdefault(p["ppid"], []).append(p)
                    if any(len(children) >= 4 for children in parents.values()):
                        observed = time.time()
            assert observed is not None, "No execution pool observed"
            schedule = [(2, "after"), (32, "before_expanded")]
            for offset, name in schedule:
                remaining = observed + offset - time.time()
                if remaining > 0:
                    time.sleep(remaining)
                script = Path(__file__).resolve().parent / f"reproduced_audit_{name}.py"
                body = script.read_text()
                # Preserve original audit artifacts; same analysis, separate destination.
                dest = evidence / f"reproduced_audit_{name}.json"
                destination_assignment = next(
                    node
                    for node in ast.parse(body).body
                    if isinstance(node, ast.Assign)
                    and any(
                        isinstance(target, ast.Name) and target.id == "destination"
                        for target in node.targets
                    )
                )
                body = body.replace(
                    ast.get_source_segment(body, destination_assignment),
                    f"destination = Path({str(dest)!r})",
                    1,
                )
                reproduction = evidence / f"reproduced_audit_{name}.py"
                reproduction.write_text(body)
                stream = (evidence / f"reproduced_audit_{name}.log").open("w")
                child = subprocess.Popen(
                    [
                        os.environ["OPENHCS_NRA_PYTHON"],
                        str(reproduction),
                    ],
                    cwd=root,
                    env={**os.environ, "OPENHCS_AUDIT_SOURCE_ROOT": str(root)},
                    stdout=stream,
                    stderr=subprocess.STDOUT,
                )
                audits.append((name, child, stream, time.time()))
            assert proc.wait(timeout=300) == 0
        finally:
            if proc.poll() is None:
                proc.terminate()
                proc.wait(timeout=30)
            resources.join()
            stopped.set()
            mem.join()
            for name, child, stream, start in audits:
                code = child.wait(timeout=90)
                stream.close()
                with (evidence / "audit_processes.jsonl").open("a") as f:
                    f.write(
                        json.dumps(
                            {
                                "name": name,
                                "pid": child.pid,
                                "start": start,
                                "artifact_completed_at": (
                                    (evidence / f"reproduced_audit_{name}.json")
                                    .stat()
                                    .st_mtime
                                    if code == 0
                                    else None
                                ),
                                "returncode": code,
                            }
                        )
                        + "\n"
                    )
    with (out / "well_throughput.csv").open() as f:
        row = next(csv.DictReader(f))
    print(
        json.dumps(
            {
                "variant": "fused_audit_overlap",
                "compile": float(row["compile_seconds"]),
                "execution": float(row["execute_seconds"]),
                "total": float(row["total_seconds"]),
                "status": row["status"],
                "output_dir": str(out),
            }
        ),
        flush=True,
    )
    (evidence / "audit_overlap_observation.json").write_text(
        json.dumps(row, indent=2) + "\n"
    )


if __name__ == "__main__":
    run()
