#!/usr/bin/env python3
"""Write the exact native-reference inventory selected for a manifest."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path

from benchmark.cellprofiler_comparison import (
    NativeReferenceArtifactProfile,
    _comparison_pipeline_params,
    _native_reference_location,
    load_comparison_cases,
)
from openhcs.core.config import GlobalPipelineConfig
from openhcs.core.equivalence.outputs import image_paths, table_paths

FIELDNAMES = (
    "case_name",
    "dataset_id",
    "reference_scope_path",
    "selected_reference_path",
    "reference_class",
    "csv_count",
    "sqlite_count",
    "cpa_properties_count",
    "image_count",
    "value_file_count",
    "value_only_image_comparison_enabled",
    "csv_plus_image",
    "csv_paths",
    "sqlite_paths",
    "cpa_properties_paths",
    "image_paths",
    "outside_selected_reference_images",
    "outside_selected_reference_csvs",
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--native-reference-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    rows = inventory_rows(args.manifest, args.native_reference_root)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=FIELDNAMES)
        writer.writeheader()
        writer.writerows(rows)

    class_counts: dict[str, int] = {}
    for row in rows:
        reference_class = str(row["reference_class"])
        class_counts[reference_class] = class_counts.get(reference_class, 0) + 1
    print(f"cases={len(rows)}")
    print(f"classes={json.dumps(class_counts, sort_keys=True)}")
    print(
        "value_only_image_comparisons="
        f"{sum(bool(row['value_only_image_comparison_enabled']) for row in rows)}"
    )
    print(f"csv_plus_image={sum(bool(row['csv_plus_image']) for row in rows)}")
    print(f"output={args.output}")
    return 0


def inventory_rows(
    manifest_path: Path,
    native_reference_root: Path,
) -> tuple[dict[str, object], ...]:
    """Return inventories rooted at the references the runner actually selects."""

    global_config = GlobalPipelineConfig()
    rows: list[dict[str, object]] = []
    for case in load_comparison_cases(Path(manifest_path)):
        effective_global_config = case.effective_global_config(global_config)
        pipeline_params = _comparison_pipeline_params(case)
        location = _native_reference_location(
            case,
            Path(native_reference_root),
            pipeline_params,
            global_config=effective_global_config,
        )
        if location.output_dir is None or location.reference_output_dir is None:
            raise FileNotFoundError(
                f"No completed native reference selected for {case.name!r}."
            )

        scope_root = location.output_dir.resolve()
        reference_root = location.reference_output_dir.resolve()
        csv_files = table_paths(reference_root)
        sqlite_files = _matching_files(reference_root, (".db", ".sqlite", ".sqlite3"))
        properties_files = _matching_files(reference_root, (".properties",))
        images = image_paths(reference_root)
        profile = NativeReferenceArtifactProfile.from_reference_output_dir(
            reference_root
        )
        outside_images = tuple(
            path
            for path in image_paths(scope_root)
            if not path.is_relative_to(reference_root)
        )
        outside_csvs = tuple(
            path
            for path in table_paths(scope_root)
            if not path.is_relative_to(reference_root)
        )
        value_file_count = len(csv_files) + len(sqlite_files) + len(images)
        rows.append(
            {
                "case_name": case.name,
                "dataset_id": case.resolved_dataset_id,
                "reference_scope_path": str(scope_root),
                "selected_reference_path": str(reference_root),
                "reference_class": _reference_class(
                    csv_files=csv_files,
                    sqlite_files=sqlite_files,
                    images=images,
                ),
                "csv_count": len(csv_files),
                "sqlite_count": len(sqlite_files),
                "cpa_properties_count": len(properties_files),
                "image_count": len(images),
                "value_file_count": value_file_count,
                "value_only_image_comparison_enabled": profile.image_only,
                "csv_plus_image": bool(csv_files and images),
                "csv_paths": _json_relative_paths(reference_root, csv_files),
                "sqlite_paths": _json_relative_paths(reference_root, sqlite_files),
                "cpa_properties_paths": _json_relative_paths(
                    reference_root, properties_files
                ),
                "image_paths": _json_relative_paths(reference_root, images),
                "outside_selected_reference_images": _json_relative_paths(
                    scope_root, outside_images
                ),
                "outside_selected_reference_csvs": _json_relative_paths(
                    scope_root, outside_csvs
                ),
            }
        )
    return tuple(rows)


def _matching_files(root: Path, suffixes: tuple[str, ...]) -> tuple[Path, ...]:
    return tuple(
        path
        for path in sorted(Path(root).rglob("*"))
        if path.is_file() and path.suffix.lower() in suffixes
    )


def _reference_class(
    *,
    csv_files: tuple[Path, ...],
    sqlite_files: tuple[Path, ...],
    images: tuple[Path, ...],
) -> str:
    if csv_files:
        return "csv"
    if sqlite_files:
        return "sqlite"
    if images and all(path.suffix.lower() == ".npy" for path in images):
        return "npy_only"
    if images:
        return "image_only"
    return "empty"


def _json_relative_paths(root: Path, paths: tuple[Path, ...]) -> str:
    return json.dumps(
        [str(path.relative_to(root)) for path in paths],
        separators=(",", ":"),
    )


if __name__ == "__main__":
    raise SystemExit(main())
