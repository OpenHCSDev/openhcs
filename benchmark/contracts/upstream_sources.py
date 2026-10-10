"""Upstream sources of benchmark manifest roots and git-backed datasets.

This module owns the manifest root acquisition declaration, each git-backed
dataset's repository and revision, and the acquired-dataset layout. It imports
only the standard library so the package build can read it (``runpy``) to
project pinned native ``.cppipe`` recipes without importing the benchmark
package.
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from enum import Enum

DATASET_DATA_DIRECTORY = "data"
"""Directory under ``<dataset cache>/<dataset id>/`` that holds acquired data."""


@dataclass(frozen=True, slots=True)
class DatasetGitSource:
    """One upstream repository and the revision a dataset is acquired at."""

    git_url: str
    git_ref: str = "HEAD"


DATASET_GIT_SOURCES: dict[str, DatasetGitSource] = {
    "CellProfiler_tutorials": DatasetGitSource(
        "https://github.com/CellProfiler/tutorials.git",
        "264a8155da21a2d468051f78211bed2e580a8934",
    ),
    "CellProfiler4_benchmark_supplement": DatasetGitSource(
        "https://github.com/carpenterlab/2021_Stirling_BMCBioInformatics.git",
        "40abc2e600fd46b74c213999dd25c5245048dc92",
    ),
    "CellOrientation_wound_healing": DatasetGitSource(
        "https://github.com/rgomez-AI/CellOrientation.git"
    ),
    "ChromTrans_3d_fish": DatasetGitSource(
        "https://github.com/rgomez-AI/3DChromTrans.git"
    ),
}


class ManifestRootAcquisitionKind(Enum):
    """Supported benchmark-manifest root acquisition families."""

    DATASET_REGISTRY = "dataset_registry"
    GIT_SPARSE = "git_sparse"


@dataclass(frozen=True, slots=True)
class ManifestRootAcquisitionSpec:
    """Declarative acquisition policy for one manifest path root."""

    kind: ManifestRootAcquisitionKind
    git_url: str | None = None
    git_ref: str = "HEAD"
    sparse_paths: tuple[str, ...] = ()
    dataset_ids: tuple[str, ...] = ()

    @classmethod
    def from_manifest(cls, raw_value: object) -> "ManifestRootAcquisitionSpec":
        """Parse an acquisition block from a benchmark manifest."""
        if not isinstance(raw_value, Mapping):
            raise ValueError("Manifest root acquisition must be an object.")
        raw_kind = raw_value.get("kind")
        if raw_kind is None:
            raise ValueError("Manifest root acquisition must declare kind.")
        try:
            kind = ManifestRootAcquisitionKind(str(raw_kind))
        except ValueError as exc:
            raise ValueError(
                f"Unsupported manifest root acquisition kind {raw_kind!r}."
            ) from exc
        raw_sparse_paths = raw_value.get("sparse_paths", ())
        raw_dataset_ids = raw_value.get("dataset_ids", ())
        git_url = raw_value.get("git_url")
        return cls(
            kind=kind,
            git_url=str(git_url) if git_url is not None else None,
            git_ref=str(raw_value.get("git_ref", "HEAD")),
            sparse_paths=_string_tuple(raw_sparse_paths, "sparse_paths"),
            dataset_ids=_string_tuple(raw_dataset_ids, "dataset_ids"),
        )


def _string_tuple(raw_value: object, field_name: str) -> tuple[str, ...]:
    """Parse a manifest string sequence."""
    if raw_value is None:
        return ()
    if isinstance(raw_value, str):
        return (raw_value,)
    if not isinstance(raw_value, Sequence):
        raise ValueError(f"Manifest acquisition {field_name} must be a sequence.")
    return tuple(str(item) for item in raw_value)
