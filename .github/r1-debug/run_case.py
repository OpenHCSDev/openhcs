"""TEMPORARY (surface R1): run named Official30 cases as the parity test does, keep outputs, print value diffs."""

import csv
import math
import os
import platform
import sys
from pathlib import Path

REPO = Path(sys.argv[1]).resolve()
OUT = Path(sys.argv[2]).resolve()
NAMES = set(sys.argv[3:])


def environment_report():
    import numba
    import numpy as np
    import scipy
    import skimage

    print("== environment")
    print("platform", platform.platform(), platform.machine(), sys.version)
    print("numpy", np.__version__, "scipy", scipy.__version__, "numba", numba.__version__, "skimage", skimage.__version__)
    print("int", np.dtype(int), "intp", np.dtype(np.intp), "long", np.dtype("l"), "longdouble", np.finfo(np.longdouble).bits)
    for key in ("NPY_DISABLE_CPU_FEATURES", "NUMBA_DISABLE_INTEL_SVML", "OPENHCS_CPU_ONLY"):
        print(key, os.environ.get(key))
    np.show_config()
    try:
        from threadpoolctl import threadpool_info

        for info in threadpool_info():
            print("threadpool", info)
    except Exception as error:  # diagnostics only
        print("threadpoolctl unavailable", error)
    from openhcs.processing.backends.cellprofiler import label_geometry

    print("svml arccos available", label_geometry._NUMPY_124_SVML_ACOS_AVAILABLE)
    probes = [0.1, 0.5, 0.7071067811865476, 0.9999, -0.3, 1 / 3, 0.123456789]
    print("acos probes", [(v, math.acos(v).hex(), float(np.arccos(v)).hex()) for v in probes])
    print("atan2 probes", [(math.atan2(a, b).hex(), float(np.arctan2(a, b)).hex()) for a, b in ((1e-9, -1.0), (0.3, 0.7), (-0.2, 0.1))])


def numeric(text):
    try:
        return float(text)
    except ValueError:
        return None


def table_diff(reference_dir, candidate_dir):
    print(f"== value diff\n reference {reference_dir}\n candidate {candidate_dir}")
    for reference in sorted(reference_dir.glob("*.csv")):
        candidate = candidate_dir / reference.name
        if not candidate.is_file():
            print(f"-- {reference.name}: no candidate table")
            continue
        ref_rows = list(csv.DictReader(reference.open(newline="")))
        cand_rows = list(csv.DictReader(candidate.open(newline="")))
        print(f"-- {reference.name}: rows {len(ref_rows)} vs {len(cand_rows)}")
        if len(ref_rows) != len(cand_rows) or not ref_rows:
            continue
        cand_columns = {c.lower(): c for c in cand_rows[0]}
        for column in ref_rows[0]:
            other = cand_columns.get(column.lower())
            if other is None:
                continue
            worst = (0.0, None)
            count = 0
            for index, (a, b) in enumerate(zip(ref_rows, cand_rows)):
                x, y = numeric(a[column]), numeric(b[other])
                if x is None or y is None or (math.isnan(x) and math.isnan(y)):
                    continue
                delta = abs(x - y)
                if delta > 1e-6 + 1e-6 * abs(x) or math.isnan(delta):
                    count += 1
                    if not delta <= worst[0]:
                        worst = (delta, (index, x, y))
            if count:
                index, x, y = worst[1]
                print(f"   {column}: {count}/{len(ref_rows)} rows differ; worst row {index}: reference {x!r} candidate {y!r} diff {y - x:+.6e}")


def main():
    environment_report()
    from benchmark.cellprofiler_comparison import load_comparison_cases, run_comparison_suite
    from openhcs.core.config import GlobalPipelineConfig, LazyNapariStreamingConfig, PartitionFilterConfig
    from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG
    from zmqruntime import DataControlPortPairAuthority

    cases = [c for c in load_comparison_cases(REPO / "benchmark/manifests/official30_portable_axis1.json") if c.name in NAMES]
    if len(cases) != len(NAMES):
        raise SystemExit(f"cases {sorted(NAMES)} resolved to {[c.name for c in cases]}")
    port = DataControlPortPairAuthority.acquire(
        OPENHCS_ZMQ_CONFIG, transport_mode=OPENHCS_ZMQ_CONFIG.transport_mode, excluded=set()
    ).data_port
    observations = run_comparison_suite(
        cases,
        output_root=OUT,
        suite_id="r1-debug",
        native_reference_root=Path(os.environ["OPENHCS_CP_NATIVE_REFERENCE_ROOT"]),
        require_native_reference=True,
        openhcs_global_config=GlobalPipelineConfig(
            partition_filter_config=PartitionFilterConfig(partition_filter=1),
            napari_streaming_config=LazyNapariStreamingConfig(enabled=False, persistent=False),
        ),
        discard_openhcs_outputs=False,
        continue_on_error=True,
        openhcs_execution_port=port,
    )
    failed = False
    for observation in observations:
        print(f"== {observation.case_name}: equivalent={observation.equivalent}")
        for side in (observation.native_cellprofiler, observation.openhcs):
            if side.error_message:
                print(side.error_message[-6000:])
        if observation.openhcs.output_path and observation.native_cellprofiler.output_path:
            table_diff(Path(observation.native_cellprofiler.output_path), Path(observation.openhcs.output_path) / "results")
        failed = failed or not observation.equivalent
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
