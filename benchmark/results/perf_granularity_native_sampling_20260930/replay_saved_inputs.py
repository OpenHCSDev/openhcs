"""Replay actual inputs against immutable original background-correction bodies."""

import argparse
import ast
import hashlib
import json
from pathlib import Path
import pickle
from statistics import median
import subprocess
import time

import cv2
import numpy as np

from openhcs.processing.backends.cellprofiler.granularity import (
    background_corrected_pixels,
)

ROOT = Path(__file__).resolve().parents[3]


def original_background_correction():
    source = subprocess.check_output(
        [
            "git",
            "show",
            "fb5fea4f1:openhcs/processing/backends/cellprofiler/granularity.py",
        ],
        cwd=ROOT,
        text=True,
    )
    # Extract original bodies without importing a second registered class family.
    names = {
        "background_corrected_pixels",
        "granularity_grey_erosion",
        "granularity_grey_dilation",
        "resample_from_cp_grid",
        "resample_between_cp_grids",
    }
    nodes = [
        node
        for node in ast.parse(source).body
        if isinstance(node, ast.FunctionDef) and node.name in names
    ]
    assert {node.name for node in nodes} == names
    reference_source = "from __future__ import annotations\n" + "\n\n".join(
        ast.get_source_segment(source, node) for node in nodes
    )
    namespace = {"np": np, "cv2": cv2}
    exec(
        compile(reference_source, "immutable-granularity-reference", "exec"), namespace
    )
    return (
        namespace["background_corrected_pixels"],
        hashlib.sha256(source.encode()).hexdigest(),
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    reference, source_digest = original_background_correction()
    records = []
    paths = sorted(args.input_dir.glob("granularity_background_*.pkl"))
    assert len(paths) == 4
    for path in paths:
        positional, keywords = pickle.loads(path.read_bytes())
        digest = hashlib.sha256(positional[0].tobytes()).hexdigest()
        expected, extent = reference(*positional, **keywords)
        actual, grid = background_corrected_pixels(*positional, **keywords)
        np.testing.assert_array_equal(actual, expected)
        np.testing.assert_array_equal(grid.logical_shape, extent)
        output_digest = hashlib.sha256(actual.tobytes()).hexdigest()
        assert output_digest == hashlib.sha256(expected.tobytes()).hexdigest()
        assert digest == hashlib.sha256(positional[0].tobytes()).hexdigest()
        samples = {"control": [], "candidate": []}
        for variant in ("control", "candidate") * 4:
            function = (
                reference if variant == "control" else background_corrected_pixels
            )
            start = time.perf_counter()
            function(*positional, **keywords)
            samples[variant].append(time.perf_counter() - start)
        records.append(
            dict(
                source=path.name,
                shape=positional[0].shape,
                dtype=str(positional[0].dtype),
                input_sha256=digest,
                output_sha256=output_digest,
                original_module_sha256=source_digest,
                all_pixels_exact=True,
                logical_shape_exact=True,
                observations=samples,
                median_seconds={
                    name: median(values) for name, values in samples.items()
                },
            )
        )
    args.output.write_text(json.dumps(records, indent=2) + "\n")
    print(json.dumps(records, indent=2))


if __name__ == "__main__":
    main()
