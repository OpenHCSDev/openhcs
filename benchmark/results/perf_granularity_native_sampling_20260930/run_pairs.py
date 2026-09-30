"""Reproduce isolated, warmed-cache granularity A/B runs."""

import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
PACKAGE = ROOT / "openhcs/processing/backends/cellprofiler"
SOURCE = PACKAGE / "granularity.py"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wells", type=int, choices=(1, 16), required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--control-native", type=Path, required=True)
    args = parser.parse_args()
    assert args.control_native.name == "_granularity_reconstruct.abi3.so"
    assert args.control_native.is_file()
    control_binary = args.control_native.resolve()
    old_target = PACKAGE / control_binary.name
    assert control_binary != old_target
    saved_binary = old_target.read_bytes() if old_target.exists() else None
    args.output_dir.mkdir(parents=True, exist_ok=False)
    saved = SOURCE.read_bytes()
    scope = json.loads(
        Path(__file__).with_name(f"scope_{args.wells}w.json").read_text()
    )
    assert (
        hashlib.sha256(saved).hexdigest() == scope["source_hashes"]["candidate"]
    ), "Check out the recorded candidate before reproduction."
    control = subprocess.check_output(
        [
            "git",
            "show",
            "fb5fea4f1:openhcs/processing/backends/cellprofiler/granularity.py",
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
    assert "NUMBA_CACHE_DIR" in env, "Use the prepared production kernel cache."
    scope["native_hashes"] = {
        path.name: hashlib.sha256(path.read_bytes()).hexdigest()
        for path in (control_binary, PACKAGE / "_granularity_native.abi3.so")
    }
    (args.output_dir / "scope.json").write_text(json.dumps(scope, indent=2) + "\n")

    def cache_state():
        return {
            str(path): (path.stat().st_mtime_ns, path.stat().st_size)
            for path in Path(env["NUMBA_CACHE_DIR"]).glob("cellprofiler*/*granularity*")
        }

    try:
        for variant, repetition in (
            ("control", 1),
            ("candidate", 1),
            ("candidate", 2),
            ("control", 2),
        ):
            if variant == "control":
                shutil.copy2(control_binary, old_target)
            else:
                old_target.unlink(missing_ok=True)
            SOURCE.write_bytes(saved if variant == "candidate" else control)
            start = time.perf_counter()
            with (args.output_dir / f"{variant}_{repetition}_warm.log").open(
                "w"
            ) as log:
                subprocess.run(
                    [
                        sys.executable,
                        "-c",
                        "from openhcs.core.callable_contract import prepare_processing_callable; "
                        "from openhcs.processing.backends.cellprofiler.granularity import measure_granularity; "
                        "prepare_processing_callable(measure_granularity)",
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
                        "1w_1t" if args.wells == 1 else "16w_4c",
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
                new_or_modified_granularity_cache_files=changes,
                output_dir=str(out),
            )
            assert result["status"] == "success" and not changes, result
            with (args.output_dir / "observations.jsonl").open("a") as stream:
                stream.write(json.dumps(result) + "\n")
            print(json.dumps(result), flush=True)
    finally:
        SOURCE.write_bytes(saved)
        if saved_binary is None:
            old_target.unlink(missing_ok=True)
        else:
            old_target.write_bytes(saved_binary)


if __name__ == "__main__":
    main()
