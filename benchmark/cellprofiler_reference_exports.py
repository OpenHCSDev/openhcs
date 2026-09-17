"""Derived CellProfiler pipelines for terminal-artifact reference exports."""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Sequence
from dataclasses import asdict, dataclass
from enum import StrEnum
from pathlib import Path

import numpy as np

from openhcs.core.artifacts import ImageArtifactType, ObjectLabelsArtifactType
from openhcs.core.equivalence.images import RuntimeImageSnapshot
from openhcs.core.equivalence.outputs import image_paths
from openhcs.interop.cellprofiler import cellprofiler_terminal_artifact_specs

_MODULE_COUNT_PATTERN = re.compile(r"^ModuleCount:(?P<count>[0-9]+)$", re.MULTILINE)
_MODULE_NUM_PATTERN = re.compile(
    r"^[A-Za-z0-9_]+:\[module_num:(?P<number>[0-9]+)\|",
    re.MULTILINE,
)


class ReferenceExportSemanticKind(StrEnum):
    """Comparison semantics for one derived reference export."""

    NUMERIC_IMAGE_PIXELS = "numeric_image_pixels"
    CATEGORICAL_OBJECT_LABELS = "categorical_object_labels"


@dataclass(frozen=True, slots=True)
class CellProfilerReferenceExportArtifact:
    """One terminal artifact and its benchmark-only file projection."""

    artifact_name: str
    artifact_type: str
    semantic_kind: ReferenceExportSemanticKind
    output_filename: str
    comparison: str

    @classmethod
    def from_terminal_spec(
        cls,
        artifact_name: str,
        artifact_type: type,
    ) -> "CellProfilerReferenceExportArtifact | None":
        """Project supported nominal artifact types into export semantics."""

        safe_name = _safe_identifier(artifact_name)
        if artifact_type is ImageArtifactType:
            return cls(
                artifact_name=artifact_name,
                artifact_type=artifact_type.__name__,
                semantic_kind=ReferenceExportSemanticKind.NUMERIC_IMAGE_PIXELS,
                output_filename=f"reference_image__{safe_name}.npy",
                comparison="float pixels: atol=1e-6, rtol=1e-6, zero mismatches",
            )
        if artifact_type is ObjectLabelsArtifactType:
            return cls(
                artifact_name=artifact_name,
                artifact_type=artifact_type.__name__,
                semantic_kind=ReferenceExportSemanticKind.CATEGORICAL_OBJECT_LABELS,
                output_filename=f"reference_labels__{safe_name}.tiff",
                comparison="integer label pixels: exact equality",
            )
        return None

    @property
    def output_stem(self) -> str:
        """Return the explicit CellProfiler single-file name."""

        return Path(self.output_filename).stem


@dataclass(frozen=True, slots=True)
class CellProfilerReferenceArtifactComparison:
    """One file-level comparison under its declared artifact semantics."""

    artifact: CellProfilerReferenceExportArtifact
    reference_path: Path
    candidate_path: Path
    reference_shape: tuple[int, ...]
    candidate_shape: tuple[int, ...]
    reference_dtype: str
    candidate_dtype: str
    reference_pixel_digest: str
    candidate_pixel_digest: str
    compared_pixel_count: int
    different_pixel_count: int | None
    out_of_tolerance_pixel_count: int | None
    max_abs_difference: float | None
    equivalent: bool

    @classmethod
    def compare(
        cls,
        artifact: CellProfilerReferenceExportArtifact,
        reference_path: Path,
        candidate_path: Path,
    ) -> "CellProfilerReferenceArtifactComparison":
        """Compare two selected files without inferring semantics from dtype."""

        reference = RuntimeImageSnapshot.from_image_file(reference_path)
        candidate = RuntimeImageSnapshot.from_image_file(candidate_path)
        reference_pixels = np.asarray(reference.pixel_data)
        candidate_pixels = np.asarray(candidate.pixel_data)
        if (
            artifact.semantic_kind
            is ReferenceExportSemanticKind.CATEGORICAL_OBJECT_LABELS
        ):
            reference_pixels, candidate_pixels = (
                _comparable_categorical_object_label_planes(
                    reference_pixels,
                    candidate_pixels,
                )
            )
        same_shape = reference_pixels.shape == candidate_pixels.shape

        different_pixel_count: int | None = None
        out_of_tolerance_pixel_count: int | None = None
        max_abs_difference: float | None = None
        equivalent = False
        if (
            same_shape
            and artifact.semantic_kind
            is ReferenceExportSemanticKind.CATEGORICAL_OBJECT_LABELS
        ):
            different_pixel_count = int(
                np.count_nonzero(reference_pixels != candidate_pixels)
            )
            equivalent = different_pixel_count == 0
        elif same_shape:
            reference_numeric = reference_pixels.astype(np.float64, copy=False)
            candidate_numeric = candidate_pixels.astype(np.float64, copy=False)
            close_pixels = np.isclose(
                reference_numeric,
                candidate_numeric,
                rtol=1e-6,
                atol=1e-6,
                equal_nan=True,
            )
            out_of_tolerance_pixel_count = int(
                close_pixels.size - np.count_nonzero(close_pixels)
            )
            absolute_differences = np.abs(reference_numeric - candidate_numeric)
            max_abs_difference = (
                float(np.nanmax(absolute_differences))
                if absolute_differences.size
                else 0.0
            )
            equivalent = out_of_tolerance_pixel_count == 0

        return cls(
            artifact=artifact,
            reference_path=Path(reference_path),
            candidate_path=Path(candidate_path),
            reference_shape=reference.shape,
            candidate_shape=candidate.shape,
            reference_dtype=reference.dtype,
            candidate_dtype=candidate.dtype,
            reference_pixel_digest=reference.pixel_digest,
            candidate_pixel_digest=candidate.pixel_digest,
            compared_pixel_count=int(reference_pixels.size) if same_shape else 0,
            different_pixel_count=different_pixel_count,
            out_of_tolerance_pixel_count=out_of_tolerance_pixel_count,
            max_abs_difference=max_abs_difference,
            equivalent=equivalent,
        )


def _comparable_categorical_object_label_planes(
    reference: np.ndarray,
    candidate: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    """Project only an explicit single-plane object-label representation.

    Object-only CellProfiler workspaces bind a two-dimensional label image as a
    one-plane stack in OpenHCS. The categorical pixels are comparable to the
    native 2-D export, but arbitrary singleton axes and true dimension
    mismatches are not normalized.
    """

    reference_pixels = np.asarray(reference)
    candidate_pixels = np.asarray(candidate)
    if (
        reference_pixels.ndim == 2
        and candidate_pixels.ndim == 3
        and candidate_pixels.shape[0] == 1
        and candidate_pixels.shape[1:] == reference_pixels.shape
    ):
        candidate_pixels = candidate_pixels[0]
    elif (
        candidate_pixels.ndim == 2
        and reference_pixels.ndim == 3
        and reference_pixels.shape[0] == 1
        and reference_pixels.shape[1:] == candidate_pixels.shape
    ):
        reference_pixels = reference_pixels[0]
    return reference_pixels, candidate_pixels


@dataclass(frozen=True, slots=True)
class CellProfilerReferenceExportPlan:
    """A source-bound plan that only appends terminal artifact exporters."""

    source_pipeline_name: str
    source_sha256: str
    artifacts: tuple[CellProfilerReferenceExportArtifact, ...]
    generated_sha256: str | None = None

    @classmethod
    def from_sidecar(cls, path: Path) -> "CellProfilerReferenceExportPlan":
        """Load the generated pipeline's declared export inventory."""

        payload = json.loads(Path(path).read_text(encoding="utf-8"))
        return cls(
            source_pipeline_name=str(payload["source_pipeline_name"]),
            source_sha256=str(payload["source_sha256"]),
            artifacts=tuple(
                CellProfilerReferenceExportArtifact(
                    artifact_name=str(artifact["artifact_name"]),
                    artifact_type=str(artifact["artifact_type"]),
                    semantic_kind=ReferenceExportSemanticKind(
                        str(artifact["semantic_kind"])
                    ),
                    output_filename=str(artifact["output_filename"]),
                    comparison=str(artifact["comparison"]),
                )
                for artifact in payload["artifacts"]
            ),
            generated_sha256=str(payload["generated_sha256"]),
        )

    @classmethod
    def from_pipeline(
        cls,
        source_pipeline: Path,
        *,
        source_root: Path,
    ) -> "CellProfilerReferenceExportPlan":
        """Derive the export inventory from importer-owned artifact contracts."""

        source_path = Path(source_pipeline)
        artifacts = tuple(
            artifact
            for spec in cellprofiler_terminal_artifact_specs(
                source_path,
                source_root=source_root,
            )
            for artifact in (
                CellProfilerReferenceExportArtifact.from_terminal_spec(
                    spec.name,
                    spec.artifact_type,
                ),
            )
            if artifact is not None
        )
        if not artifacts:
            raise ValueError(
                f"CellProfiler pipeline {source_path} has no terminal image or "
                "object-label artifacts to export."
            )
        names = tuple(artifact.artifact_name for artifact in artifacts)
        if len(set(names)) != len(names):
            raise ValueError(
                f"CellProfiler pipeline {source_path} has ambiguous terminal "
                f"artifact names: {names!r}."
            )
        return cls(
            source_pipeline_name=source_path.name,
            source_sha256=hashlib.sha256(source_path.read_bytes()).hexdigest(),
            artifacts=artifacts,
        )

    def validate_generated_pipeline(self, path: Path) -> None:
        """Require a sidecar plan to describe the exact generated pipeline."""

        if self.generated_sha256 is None:
            raise ValueError("Reference export plan has no generated-pipeline digest.")
        generated_path = Path(path)
        observed_sha256 = hashlib.sha256(generated_path.read_bytes()).hexdigest()
        if observed_sha256 != self.generated_sha256:
            raise ValueError(
                "Reference export sidecar does not describe generated pipeline "
                f"{generated_path}: expected sha256={self.generated_sha256}, "
                f"observed sha256={observed_sha256}."
            )

    def compare_output_roots(
        self,
        reference_root: Path,
        candidate_root: Path,
    ) -> tuple[CellProfilerReferenceArtifactComparison, ...]:
        """Compare the exact declared output inventory under owned semantics."""

        reference_paths = self._declared_output_paths(
            image_paths(reference_root),
            "reference",
            require_exact_inventory=True,
        )
        candidate_paths = self._declared_output_paths(
            image_paths(candidate_root),
            "candidate",
            require_exact_inventory=True,
        )
        return self._compare_declared_paths(reference_paths, candidate_paths)

    def compare_observed_outputs(
        self,
        reference_root: Path,
        candidate_paths: Sequence[Path],
    ) -> tuple[CellProfilerReferenceArtifactComparison, ...]:
        """Compare declared exports selected from runtime-observed output paths."""

        reference_paths = self._declared_output_paths(
            image_paths(reference_root),
            "reference",
            require_exact_inventory=True,
        )
        selected_candidate_paths = self._declared_output_paths(
            candidate_paths,
            "candidate",
            require_exact_inventory=False,
        )
        return self._compare_declared_paths(
            reference_paths,
            selected_candidate_paths,
        )

    def _compare_declared_paths(
        self,
        reference_paths: dict[str, Path],
        candidate_paths: dict[str, Path],
    ) -> tuple[CellProfilerReferenceArtifactComparison, ...]:
        """Apply each declaration's semantic comparison to selected paths."""

        return tuple(
            CellProfilerReferenceArtifactComparison.compare(
                artifact,
                reference_paths[artifact.output_filename],
                candidate_paths[artifact.output_filename],
            )
            for artifact in self.artifacts
        )

    def _declared_output_paths(
        self,
        output_paths: Sequence[Path],
        side: str,
        *,
        require_exact_inventory: bool,
    ) -> dict[str, Path]:
        """Select exactly one image file for each declaration-owned export."""

        observed: dict[str, list[Path]] = {}
        for path in output_paths:
            observed.setdefault(path.name, []).append(path)
        expected_names = {artifact.output_filename for artifact in self.artifacts}
        observed_names = set(observed)
        missing_names = expected_names - observed_names
        unexpected_names = (
            observed_names - expected_names if require_exact_inventory else set()
        )
        if missing_names or unexpected_names:
            raise ValueError(
                f"{side} output inventory differs: "
                f"expected={sorted(expected_names)!r}, "
                f"observed={sorted(observed_names)!r}."
            )
        duplicates = {
            name: tuple(str(path) for path in paths)
            for name, paths in observed.items()
            if len(paths) != 1
        }
        if duplicates:
            raise ValueError(
                f"{side} output inventory contains duplicate declared names: "
                f"{duplicates!r}."
            )
        return {name: paths[0] for name, paths in observed.items()}

    def render(self, source_text: str) -> str:
        """Append exporters without changing existing modules or settings."""

        module_numbers = tuple(
            int(match.group("number"))
            for match in _MODULE_NUM_PATTERN.finditer(source_text)
        )
        if not module_numbers:
            raise ValueError("Reference export source contains no modules.")
        first_module_num = max(module_numbers) + 1
        blocks: list[str] = []
        next_module_num = first_module_num
        for artifact in self.artifacts:
            export_image_name = artifact.artifact_name
            if (
                artifact.semantic_kind
                is ReferenceExportSemanticKind.CATEGORICAL_OBJECT_LABELS
            ):
                export_image_name = "OpenHCSReferenceLabels_" + _safe_identifier(
                    artifact.artifact_name
                )
                blocks.append(
                    _convert_objects_to_image_block(
                        module_num=next_module_num,
                        object_name=artifact.artifact_name,
                        image_name=export_image_name,
                    )
                )
                next_module_num += 1
            blocks.append(
                _save_images_block(
                    module_num=next_module_num,
                    image_name=export_image_name,
                    output_stem=artifact.output_stem,
                    categorical=(
                        artifact.semantic_kind
                        is ReferenceExportSemanticKind.CATEGORICAL_OBJECT_LABELS
                    ),
                )
            )
            next_module_num += 1

        added_module_count = next_module_num - first_module_num
        match = _MODULE_COUNT_PATTERN.search(source_text)
        if match is None:
            raise ValueError("Reference export source has no ModuleCount header.")
        declared_count = int(match.group("count"))
        rendered = _MODULE_COUNT_PATTERN.sub(
            f"ModuleCount:{declared_count + added_module_count}",
            source_text,
            count=1,
        )
        return rendered.rstrip() + "\n\n" + "\n\n".join(blocks) + "\n"

    def materialize(
        self,
        source_pipeline: Path,
        output_pipeline: Path,
        *,
        provenance: dict[str, object] | None = None,
    ) -> Path:
        """Write the derived pipeline and a machine-readable provenance sidecar."""

        source_path = Path(source_pipeline)
        if hashlib.sha256(source_path.read_bytes()).hexdigest() != self.source_sha256:
            raise ValueError(
                f"CellProfiler source changed after plan creation: {source_path}."
            )
        destination = Path(output_pipeline)
        destination.parent.mkdir(parents=True, exist_ok=True)
        rendered = self.render(source_path.read_text(encoding="utf-8"))
        destination.write_text(rendered, encoding="utf-8")
        sidecar_payload = {
            "schema_version": 1,
            "derivation": "append_declaration_derived_terminal_artifact_exports",
            "source_pipeline_name": self.source_pipeline_name,
            "source_sha256": self.source_sha256,
            "generated_sha256": hashlib.sha256(destination.read_bytes()).hexdigest(),
            "artifacts": [asdict(artifact) for artifact in self.artifacts],
            "provenance": provenance or {},
        }
        destination.with_suffix(".reference_exports.json").write_text(
            json.dumps(sidecar_payload, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        return destination


def _safe_identifier(value: str) -> str:
    """Return a stable file/module identifier for a declared artifact name."""

    resolved = "".join(character if character.isalnum() else "_" for character in value)
    resolved = resolved.strip("_")
    if not resolved:
        raise ValueError(f"Artifact name has no safe identifier characters: {value!r}.")
    return resolved


def _convert_objects_to_image_block(
    *,
    module_num: int,
    object_name: str,
    image_name: str,
) -> str:
    """Render CellProfiler 4's lossless object-label image projection."""

    return f"""ConvertObjectsToImage:[module_num:{module_num}|svn_version:'Unknown'|variable_revision_number:1|show_window:False|notes:['Benchmark-only export of terminal object labels; processing settings above are unchanged.']|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input objects:{object_name}
    Name the output image:{image_name}
    Select the color format:uint16
    Select the colormap:Default"""


def _save_images_block(
    *,
    module_num: int,
    image_name: str,
    output_stem: str,
    categorical: bool,
) -> str:
    """Render one deterministic CellProfiler 4 image export module."""

    file_format = "tiff" if categorical else "npy"
    bit_depth = "16-bit integer" if categorical else "32-bit floating point"
    return f"""SaveImages:[module_num:{module_num}|svn_version:'Unknown'|variable_revision_number:16|show_window:False|notes:['Benchmark-only export of an existing terminal artifact; processing settings above are unchanged.']|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the type of image to save:Image
    Select the image to save:{image_name}
    Select method for constructing file names:Single name
    Select image name for file prefix:None
    Enter single file name:{output_stem}
    Number of digits:4
    Append a suffix to the image file name?:No
    Text to append to the image name:
    Saved file format:{file_format}
    Output file location:Default Output Folder|
    Image bit depth:{bit_depth}
    Overwrite existing files without warning?:Yes
    When to save:Every cycle
    Record the file and path information to the saved image?:No
    Create subfolders in the output folder?:No
    Base image folder:Elsewhere...|
    How to save the series:T (Time)
    Save with lossless compression?:Yes"""
