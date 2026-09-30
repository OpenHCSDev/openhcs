"""Reproduce warmed-cache radial A/B runs on the recorded candidate source."""

import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
SOURCE = ROOT / "openhcs/processing/backends/cellprofiler/intensity_distribution.py"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wells", type=int, choices=(1, 16), required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=False)
    mode = "1w_1t" if args.wells == 1 else "16w_4c"
    saved = SOURCE.read_bytes()
    expected = json.loads(
        Path(__file__).with_name(f"scope_{args.wells}w.json").read_text()
    )["source_hashes"]["candidate"]
    assert (
        hashlib.sha256(saved).hexdigest() == expected
    ), "Check out the recorded candidate before reproduction."
    control = subprocess.check_output(
        [
            "git",
            "show",
            "32d070c26:openhcs/processing/backends/cellprofiler/intensity_distribution.py",
        ],
        cwd=ROOT,
    )
    env = os.environ.copy()
    env.update(
        OPENHCS_CPU_ONLY="true",
        OPENHCS_SUBPROCESS_NO_GPU="1",
        POLYSTORE_SUBPROCESS_NO_GPU="1",
    )
    for name in (
        "OPENHCS_WORKER_PROFILE_DIR",
        "NUMBA_ENABLE_SYS_MONITORING",
        "OPENHCS_PROFILE_FUNCTION_RUNTIME",
        "NUMBA_DEBUG_CACHE",
    ):
        env.pop(name, None)
    assert (
        "NUMBA_CACHE_DIR" in env
    ), "Point NUMBA_CACHE_DIR at the prepared production kernel cache."

    def cache_state():
        return {
            str(p): (p.stat().st_mtime_ns, p.stat().st_size)
            for p in Path(env["NUMBA_CACHE_DIR"]).glob(
                "cellprofiler*/*intensity_distribution*"
            )
        }

    try:
        for variant, repetition in (
            ("control", 1),
            ("candidate", 1),
            ("candidate", 2),
            ("control", 2),
        ):
            SOURCE.write_bytes(saved if variant == "candidate" else control)
            start = time.perf_counter()
            with (args.output_dir / f"{variant}_{repetition}_warm.log").open(
                "w"
            ) as log:
                subprocess.run(
                    [
                        sys.executable,
                        "-c",
                        "from openhcs.processing.backends.cellprofiler.intensity_distribution import RadialDistributionBackendStrategy; RadialDistributionBackendStrategy.prepare_registered_family()",
                    ],
                    cwd=ROOT,
                    env=env,
                    stdout=log,
                    stderr=subprocess.STDOUT,
                    check=True,
                    timeout=90,
                )
            preparation_seconds = time.perf_counter() - start
            before = cache_state()
            out = args.output_dir / f"{variant}_{repetition}"
            with (args.output_dir / f"{variant}_{repetition}.log").open("w") as log:
                subprocess.run(
                    [
                        sys.executable,
                        "scripts/benchmark_cppipe_well_throughput.py",
                        "--manifest",
                        "benchmark/manifests/official30_portable_axis1.json",
                        "--output-dir",
                        str(out),
                        "--mode",
                        mode,
                        "--case",
                        "ExampleImagingFlowCytometryObjectsInGrid",
                    ],
                    cwd=ROOT,
                    env=env,
                    stdout=log,
                    stderr=subprocess.STDOUT,
                    check=True,
                    timeout=240,
                )
            after = cache_state()
            changes = {
                name: value
                for name, value in after.items()
                if before.get(name) != value
            }
            with (out / "well_throughput.csv").open() as stream:
                row = next(csv.DictReader(stream))
            result = dict(
                variant=variant,
                repetition=repetition,
                warming_seconds=preparation_seconds,
                compile=float(row["compile_seconds"]),
                execution=float(row["execute_seconds"]),
                total=float(row["total_seconds"]),
                status=row["status"],
                new_or_modified_radial_cache_files=changes,
                output_dir=str(out),
            )
            assert result["status"] == "success" and not changes, result
            with (args.output_dir / "observations.jsonl").open("a") as stream:
                stream.write(json.dumps(result) + "\n")
            print(json.dumps(result), flush=True)
    finally:
        SOURCE.write_bytes(saved)


if __name__ == "__main__":
    main()
