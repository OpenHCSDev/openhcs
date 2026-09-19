"""Independent pilot corpus preparation and scoring, separate from agent inputs.

This module never authors pipelines. Saved predictions are decoded by PolyStore,
the disk reader used by OpenHCS; only scalar 2D labels (or singleton wrappers)
are accepted. It never guesses non-singleton axes or scores a display overlay.
"""

from __future__ import annotations

import argparse
import csv
from abc import ABC, abstractmethod
from dataclasses import dataclass
from enum import Enum
import hashlib
import io
import json
from pathlib import Path
from urllib.parse import unquote
from zipfile import ZipFile
from collections.abc import Iterator
from metaclass_registry import AutoRegisterMeta
from openhcs.serialization.json import to_jsonable
from openhcs.core.runtime_measurements import MeasurementRowAxisField
from openhcs.processing.backends.cellprofiler.intensity import (
    MeasureObjectIntensityModule,
)
from pydantic import TypeAdapter

import numpy as np
from scipy import ndimage
from scipy.optimize import linear_sum_assignment
from skimage.measure import label
from polystore.constants import Backend
from polystore.filemanager import FileManager
from polystore.disk import DiskStorageBackend
import tifffile
import imageio.v3 as iio


class DatasetId(str, Enum):
    NUCLEI_039 = "BBBC039"
    CELLS_007 = "BBBC007"
    TRANSLOCATION_013 = "BBBC013"


class Partition(str, Enum):
    DEVELOPMENT = "development"
    HELD_OUT = "held_out"


class ScientificTask(str, Enum):
    NUCLEAR_INSTANCES = "nuclear_instances"
    SEEDED_CELLS = "seeded_cells"
    TRANSLOCATION = "translocation"


class InputEncoding(str, Enum):
    SCALAR = "scalar_grayscale"
    CORNER_REGISTRATION_RGB = "RGB_median_removes_colored_corner_registration_strokes"


@dataclass(frozen=True)
class InputChannel:
    identity: str
    filename: str
    original_member: str
    source_sha256: str
    file_sha256: str
    pixel_sha256: str
    shape: tuple[int, int]
    dtype: str
    conversion: InputEncoding
    colored_registration_pixels: int


@dataclass(frozen=True)
class EvaluationField:
    dataset: DatasetId
    task: ScientificTask
    partition: Partition
    field_id: str
    channels: tuple[InputChannel, ...]
    annotations: tuple[str, ...]
    reference_identity: str


@dataclass(frozen=True)
class FileChecksum:
    filename: str
    sha256: str
    bytes: int | None = None


@dataclass(frozen=True)
class FrozenPredictionSet:
    """Prediction bytes frozen before an evaluator may open annotations."""

    root: Path
    manifest: FileChecksum
    artifacts: tuple[FileChecksum, ...]

    @classmethod
    def from_sha256sum(cls, root: Path, manifest_path: Path) -> FrozenPredictionSet:
        artifacts = []
        seen = set()
        for line in manifest_path.read_text().splitlines():
            digest, separator, filename = line.partition("  ")
            if not separator or len(digest) != 64:
                raise ValueError(f"Invalid SHA256 manifest line: {line!r}")
            relative = Path(filename)
            if relative.is_absolute() or ".." in relative.parts:
                raise ValueError(f"Prediction path escapes the trial root: {filename}")
            if filename in seen:
                raise ValueError(f"Duplicate prediction path: {filename}")
            seen.add(filename)
            path = root / relative
            if not path.is_file() or sha256(path) != digest:
                raise ValueError(f"Frozen prediction checksum mismatch: {filename}")
            artifacts.append(FileChecksum(filename, digest, path.stat().st_size))
        return cls(
            root,
            FileChecksum(
                str(manifest_path), sha256(manifest_path), manifest_path.stat().st_size
            ),
            tuple(artifacts),
        )

    def unique_source_artifact(self, source_filename: str, suffix: str) -> Path:
        source_name = Path(source_filename).name
        matches = tuple(
            artifact
            for artifact in self.artifacts
            if unquote(Path(artifact.filename).name).startswith(f"{source_name}_")
            and artifact.filename.endswith(suffix)
        )
        if len(matches) != 1:
            raise ValueError(
                f"Expected one {suffix} artifact for {source_filename}; "
                f"found {len(matches)}"
            )
        return self.root / matches[0].filename

    def unique_component_artifact(
        self,
        field_id: str,
        channel_index: int,
        suffix: str,
    ) -> Path:
        """Resolve one persisted artifact by prepared semantic components."""

        component_prefix = f"{field_id}_w{channel_index}_"
        matches = tuple(
            artifact
            for artifact in self.artifacts
            if unquote(Path(artifact.filename).name).startswith(component_prefix)
            and artifact.filename.endswith(suffix)
        )
        if len(matches) != 1:
            raise ValueError(
                f"Expected one {suffix} artifact for {field_id} channel "
                f"{channel_index}; found {len(matches)}"
            )
        return self.root / matches[0].filename


@dataclass(frozen=True)
class PredictionFreezeReceipt:
    root: Path
    prediction_directory: Path
    manifest: FileChecksum
    artifact_count: int
    total_bytes: int


def freeze_prediction_directory(
    root: Path,
    prediction_directory: Path,
    manifest_path: Path,
) -> PredictionFreezeReceipt:
    """Freeze one prediction directory before evaluator access begins."""
    if manifest_path.exists():
        raise FileExistsError(f"Prediction manifest already exists: {manifest_path}")
    root = root.resolve()
    prediction_directory = prediction_directory.resolve()
    try:
        prediction_directory.relative_to(root)
    except ValueError as exc:
        raise ValueError("Prediction directory must be within the trial root") from exc
    paths = tuple(
        sorted(path for path in prediction_directory.rglob("*") if path.is_file())
    )
    if not paths:
        raise ValueError(f"Prediction directory is empty: {prediction_directory}")
    payload = "".join(f"{sha256(path)}  {path.relative_to(root)}\n" for path in paths)
    manifest_path.write_text(payload)
    return PredictionFreezeReceipt(
        root,
        prediction_directory,
        FileChecksum(
            str(manifest_path), sha256(manifest_path), manifest_path.stat().st_size
        ),
        len(paths),
        sum(path.stat().st_size for path in paths),
    )


@dataclass(frozen=True)
class CorpusReceipt:
    protocol_version: int
    selection: str
    annotations_are_not_agent_inputs: bool
    archives: tuple[FileChecksum, ...]
    fields: tuple[EvaluationField, ...]
    annotation_files: tuple[FileChecksum, ...]


@dataclass(frozen=True)
class SelectedChannel:
    index: int
    identity: str
    archive: ZipFile
    member: str


@dataclass(frozen=True)
class SelectedAnnotation:
    directory: str
    name: str
    archive: ZipFile
    member: str


@dataclass(frozen=True)
class FieldSelection:
    partition: Partition
    field_id: str
    channels: tuple[SelectedChannel, ...]
    annotations: tuple[SelectedAnnotation, ...]
    reference_identity: str


@dataclass(frozen=True)
class NormalizedPixels:
    image: np.ndarray
    conversion: InputEncoding = InputEncoding.SCALAR
    colored_registration_pixels: int = 0


@dataclass(frozen=True)
class PredictionArtifacts:
    nuclei_labels: Path
    cell_labels: Path | None = None


@dataclass(frozen=True)
class InstanceMetrics:
    iou_threshold: float
    true_instances: int
    predicted_instances: int
    matched: int
    false_positive: int
    false_negative: int
    precision: float | None
    recall: float | None
    object_f1: float
    pixel_dice: float
    split_truth_instances_overlap_ge_10pct: int
    merged_predicted_instances_overlap_ge_10pct: int
    count_error: int


@dataclass(frozen=True)
class BoundaryMetrics:
    relevant_boundary_pixels: int
    within_2px: int
    adjacent_boundary_within_2px_fraction: float | None
    correspondence: str = "nearest_union_of_monochrome_manual_outlines"
    limitation: str = (
        "Directed precision can reward incomplete segmentation; end-to-end raw-image trial differs from published manual-seed/foreground baseline. No manual object correspondence is inferred."
    )


@dataclass(frozen=True)
class NuclearFieldScore:
    prediction: FileChecksum
    truth: FileChecksum
    metrics: InstanceMetrics


@dataclass(frozen=True)
class CellFieldScore:
    nuclei_prediction: FileChecksum
    cells_prediction: FileChecksum
    manual_nucleus_closed_interiors: int
    manual_nucleus_frame_or_open_regions_excluded: int
    nuclear_count_error_vs_closed_interiors: int
    predicted_cell_count: int
    predicted_nucleus_count: int
    nuclei_without_cell_overlap: int
    extra_nuclei_sharing_a_predicted_cell: int
    boundary: BoundaryMetrics
    nuclear_count_limitation: str = (
        "Incomplete frame/open contours excluded; interior areas omit outline strokes. Not exhaustive spatial instance truth."
    )


ScientificFieldScore = NuclearFieldScore | CellFieldScore


@dataclass(frozen=True)
class NuclearPartitionMetrics:
    fields: int
    true_instances: int
    predicted_instances: int
    matched: int
    false_positive: int
    false_negative: int
    precision: float | None
    recall: float | None
    object_f1: float
    mean_field_object_f1: float
    mean_field_pixel_dice: float
    split_truth_instances_overlap_ge_10pct: int
    merged_predicted_instances_overlap_ge_10pct: int
    count_error: int


@dataclass(frozen=True)
class NuclearPartitionScore:
    dataset: DatasetId
    partition: Partition
    corpus_manifest: FileChecksum
    prediction_manifest: FileChecksum
    fields: tuple[NuclearFieldScore, ...]
    metrics: NuclearPartitionMetrics


@dataclass(frozen=True)
class CellPartitionMetrics:
    fields: int
    manual_nucleus_closed_interiors: int
    manual_nucleus_frame_or_open_regions_excluded: int
    predicted_nucleus_count: int
    nuclear_count_error_vs_closed_interiors: int
    predicted_cell_count: int
    nuclei_without_cell_overlap: int
    extra_nuclei_sharing_a_predicted_cell: int
    relevant_boundary_pixels: int
    boundary_pixels_within_2px: int
    pooled_adjacent_boundary_within_2px_fraction: float | None
    mean_field_adjacent_boundary_within_2px_fraction: float | None


@dataclass(frozen=True)
class CellPartitionScore:
    dataset: DatasetId
    partition: Partition
    corpus_manifest: FileChecksum
    prediction_manifest: FileChecksum
    fields: tuple[CellFieldScore, ...]
    metrics: CellPartitionMetrics


class DatasetDeclaration(ABC, metaclass=AutoRegisterMeta):
    """Accession-owned scientific task, acquisition and evaluation policy."""

    __registry_key__ = "dataset_id"
    dataset_id: DatasetId | None = None
    task: ScientificTask
    selection_description: str

    @abstractmethod
    def selections(self, root: Path) -> Iterator[FieldSelection]:
        """Yield selections while their annotation/image archives remain open."""

    def normalize(self, image: np.ndarray, member: str) -> NormalizedPixels:
        if image.ndim != 2:
            raise ValueError(
                f"Expected one grayscale XY field: {member}: {image.shape}"
            )
        return NormalizedPixels(image)

    def extra_evaluation_files(self, root: Path) -> tuple[Path, ...]:
        return ()

    def materialize_evaluation_metadata(self, root: Path) -> None:
        """Optional dataset-owned metadata write, never invoked by the audit."""

    def annotation_shape(self, path: Path) -> tuple[int, int]:
        return read_labels(path).shape

    def prepare_fields(self, root: Path) -> tuple[EvaluationField, ...]:
        fields = []
        for selected in self.selections(root):
            channels = tuple(
                normalized_input(
                    root, self, selected.partition, selected.field_id, channel
                )
                for channel in selected.channels
            )
            annotations = tuple(
                save_annotation(
                    root,
                    self.dataset_id,
                    annotation.directory,
                    annotation.name,
                    annotation.archive,
                    annotation.member,
                )
                for annotation in selected.annotations
            )
            fields.append(
                EvaluationField(
                    self.dataset_id,
                    self.task,
                    selected.partition,
                    selected.field_id,
                    channels,
                    annotations,
                    selected.reference_identity,
                )
            )
        self.materialize_evaluation_metadata(root)
        return tuple(fields)

    @abstractmethod
    def score(
        self, predictions: PredictionArtifacts, root: Path, field: EvaluationField
    ) -> ScientificFieldScore:
        """Score saved artifacts against this field's independent references."""


def sha256(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def decode_source(channel: SelectedChannel) -> tuple[bytes, np.ndarray]:
    """Decode archive payloads without assigning scientific channel semantics."""
    payload = channel.archive.read(channel.member)
    suffix = Path(channel.member).suffix.lower()
    image = (
        tifffile.imread(io.BytesIO(payload))
        if suffix == ".tif"
        else iio.imread(payload, extension=suffix)
    )
    return payload, image


def normalized_input(
    root: Path,
    declaration: DatasetDeclaration,
    partition: Partition,
    field_id: str,
    channel: SelectedChannel,
) -> InputChannel:
    payload, image = decode_source(channel)
    normalized = declaration.normalize(image, channel.member)
    image = normalized.image
    path = (
        root
        / "inputs"
        / declaration.dataset_id.value
        / partition.value
        / f"{field_id}_s001_w{channel.index}_z001_t001.tif"
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    tifffile.imwrite(path, image, photometric="minisblack", metadata={"axes": "YX"})
    return InputChannel(
        channel.identity,
        str(path.relative_to(root)),
        channel.member,
        hashlib.sha256(payload).hexdigest(),
        sha256(path),
        hashlib.sha256(image.tobytes()).hexdigest(),
        image.shape,
        str(image.dtype),
        normalized.conversion,
        normalized.colored_registration_pixels,
    )


def save_annotation(
    root: Path,
    dataset: DatasetId,
    field_id: str,
    name: str,
    archive: ZipFile,
    member: str,
) -> str:
    path = root / "evaluation" / dataset.value / field_id / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(archive.read(member))
    return str(path.relative_to(root))


class Nuclei039(DatasetDeclaration):
    dataset_id = DatasetId.NUCLEI_039
    task = ScientificTask.NUCLEAR_INSTANCES
    selection_description = "039: lexicographic first4 official validation, all50 test"

    def annotation_shape(self, path: Path) -> tuple[int, int]:
        return decode_039(path).shape

    def selections(self, root: Path) -> Iterator[FieldSelection]:
        archives = root / "archives"
        with (
            ZipFile(archives / "BBBC039_images.zip") as images,
            ZipFile(archives / "BBBC039_masks.zip") as masks,
            ZipFile(archives / "BBBC039_metadata.zip") as metadata,
        ):
            for partition, split, cap in (
                (Partition.DEVELOPMENT, "validation", 4),
                (Partition.HELD_OUT, "test", 50),
            ):
                selected = sorted(
                    metadata.read(f"metadata/{split}.txt").decode().splitlines()
                )[:cap]
                for index, name in enumerate(selected, 1):
                    field_id = f"A{index:02d}"
                    yield FieldSelection(
                        partition,
                        field_id,
                        (
                            SelectedChannel(
                                1,
                                "Hoechst DNA",
                                images,
                                f"images/{Path(name).stem}.tif",
                            ),
                        ),
                        (
                            SelectedAnnotation(
                                f"{partition.value}_{field_id}",
                                "nuclei.png",
                                masks,
                                f"masks/{name}",
                            ),
                        ),
                        f"official_{split}:{name}",
                    )

    def materialize_evaluation_metadata(self, root: Path) -> None:
        with ZipFile(root / "archives" / "BBBC039_metadata.zip") as metadata:
            for split in ("training", "validation", "test"):
                path = root / "evaluation" / self.dataset_id.value / f"{split}.txt"
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(metadata.read(f"metadata/{split}.txt"))

    def extra_evaluation_files(self, root: Path) -> tuple[Path, ...]:
        return tuple(
            root / "evaluation" / self.dataset_id.value / f"{split}.txt"
            for split in ("training", "validation", "test")
        )

    def score(
        self, predictions: PredictionArtifacts, root: Path, field: EvaluationField
    ) -> NuclearFieldScore:
        return score_039(predictions.nuclei_labels, root / field.annotations[0])


class Cells007(DatasetDeclaration):
    dataset_id = DatasetId.CELLS_007
    task = ScientificTask.SEEDED_CELLS
    selection_description = (
        "007: SHA256(slas-20260915:basename) first4 development/rest heldout"
    )

    def normalize(self, image: np.ndarray, member: str) -> NormalizedPixels:
        if image.ndim == 2:
            return super().normalize(image, member)
        if image.ndim != 3 or image.shape[2] != 3:
            raise ValueError(
                f"Not inspected scalar/RGB007 encoding: {member}: {image.shape}"
            )
        colored = np.any(image != image[:, :, :1], axis=2)
        yy, xx = np.nonzero(colored)
        if np.any((yy >= 30) & (yy < image.shape[0] - 30)) or np.any(
            (xx >= 30) & (xx < image.shape[1] - 30)
        ):
            raise ValueError(
                f"Colored pixels outside inspected corner registration marks: {member}"
            )
        return NormalizedPixels(
            np.median(image, axis=2).astype(image.dtype),
            InputEncoding.CORNER_REGISTRATION_RGB,
            int(colored.sum()),
        )

    def selections(self, root: Path) -> Iterator[FieldSelection]:
        archives = root / "archives"
        with (
            ZipFile(archives / "BBBC007_images.zip") as images,
            ZipFile(archives / "BBBC007_outlines.zip") as outlines,
        ):
            pairs = []
            for member in images.namelist():
                if member.endswith("_D_1UL.tif"):
                    pairs.append((member, member.replace("_D_1UL.tif", "_F_2UL.tif")))
                elif member.startswith("BBBC007_v1_images/A9/") and member.endswith(
                    "d.tif"
                ):
                    pairs.append((member, member.removesuffix("d.tif") + "f.tif"))
                elif member.startswith("BBBC007_v1_images/f113/") and member.endswith(
                    "d0.tif"
                ):
                    pairs.append((member, member.removesuffix("d0.tif") + "d1.tif"))
            pairs.sort(
                key=lambda pair: hashlib.sha256(
                    ("slas-20260915:" + Path(pair[0]).name).encode()
                ).hexdigest()
            )
            if len(pairs) != 16:
                raise ValueError(
                    f"Expected16annotated paired fields; found{len(pairs)}"
                )
            for index, (dna, actin) in enumerate(pairs, 1):
                partition = Partition.DEVELOPMENT if index <= 4 else Partition.HELD_OUT
                field_id = f"A{index:02d}"
                channels = (
                    SelectedChannel(1, "DNA", images, dna),
                    SelectedChannel(2, "Actin", images, actin),
                )
                annotations = tuple(
                    SelectedAnnotation(
                        field_id,
                        name,
                        outlines,
                        source.replace("BBBC007_v1_images/", "BBBC007_v1_outlines/"),
                    )
                    for name, source in (
                        ("nuclei_outlines.tif", dna),
                        ("cell_outlines.tif", actin),
                    )
                )
                yield FieldSelection(
                    partition,
                    field_id,
                    channels,
                    annotations,
                    Path(dna).name.removesuffix("_D_1UL.tif"),
                )

    def score(
        self, predictions: PredictionArtifacts, root: Path, field: EvaluationField
    ) -> CellFieldScore:
        if predictions.cell_labels is None:
            raise ValueError("Cell labels are required for BBBC007")
        return score_007(
            predictions.nuclei_labels,
            predictions.cell_labels,
            root / field.annotations[0],
            root / field.annotations[1],
        )


class Translocation013(DatasetDeclaration):
    dataset_id = DatasetId.TRANSLOCATION_013
    task = ScientificTask.TRANSLOCATION
    selection_description = "013: A04,B08,E04,F08 development/rest heldout"

    def selections(self, root: Path) -> Iterator[FieldSelection]:
        archives = root / "archives"
        with ZipFile(archives / "BBBC013_images.zip") as images:
            for index in range(96):
                row, column = "ABCDEFGH"[index // 12], index % 12 + 1
                well = f"{row}{column:02d}"
                partition = (
                    Partition.DEVELOPMENT
                    if well in {"A04", "B08", "E04", "F08"}
                    else Partition.HELD_OUT
                )
                channels = tuple(
                    SelectedChannel(
                        channel,
                        identity,
                        images,
                        f"BBBC013_v1_images_bmp/Channel{channel}-{index + 1:02d}-{row}-{column:02d}.BMP",
                    )
                    for channel, identity in ((1, "FKHR-GFP"), (2, "DRAQ DNA"))
                )
                yield FieldSelection(partition, well, channels, (), well)

    def materialize_evaluation_metadata(self, root: Path) -> None:
        doses = [
            float(value)
            for value in (root / "archives" / "BBBC013_platemap_all.txt")
            .read_text()
            .splitlines()
            if value and not value.startswith("DESCRIPTION")
        ]
        if len(doses) != 96:
            raise ValueError(f"Expected96 row-major doses, found{len(doses)}")
        plate = []
        for index, dose in enumerate(doses):
            row, column = "ABCDEFGH"[index // 12], index % 12 + 1
            treatment = Treatment.WORTMANNIN if row <= "D" else Treatment.LY294002
            role = PlateRole.DOSE
            if column in (1, 12):
                positive = (treatment is Treatment.WORTMANNIN and column == 12) or (
                    treatment is Treatment.LY294002 and column == 1
                )
                role = PlateRole.POSITIVE if positive else PlateRole.NEGATIVE
            elif column == 2:
                role = PlateRole.EMPTY
            plate.append(
                PlateWell(
                    f"{row}{column:02d}",
                    treatment,
                    dose,
                    "nM" if row <= "D" else "uM",
                    role,
                )
            )
        path = self.extra_evaluation_files(root)[0]
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(to_jsonable(plate), indent=2) + "\n")

    def extra_evaluation_files(self, root: Path) -> tuple[Path, ...]:
        return (root / "evaluation" / self.dataset_id.value / "plate_map.json",)

    def score(
        self, predictions: PredictionArtifacts, root: Path, field: EvaluationField
    ) -> ScientificFieldScore:
        raise ValueError(
            "BBBC013 requires saved cell-level intensity measurements and well aggregation, not object masks as ground truth"
        )


class Treatment(str, Enum):
    WORTMANNIN = "Wortmannin"
    LY294002 = "LY294002"


class PlateRole(str, Enum):
    POSITIVE = "positive"
    NEGATIVE = "negative"
    EMPTY = "empty"
    DOSE = "dose"


@dataclass(frozen=True)
class PlateWell:
    well: str
    treatment: Treatment
    dose: float
    unit: str
    role: PlateRole


def prepare(root: Path) -> CorpusReceipt:
    """Materialize declaration-owned selections through one common mechanism."""
    declarations = tuple(
        declaration() for declaration in DatasetDeclaration.__registry__.values()
    )
    fields = tuple(
        field
        for declaration in declarations
        for field in declaration.prepare_fields(root)
    )
    annotation_paths = {root / name for field in fields for name in field.annotations}
    annotation_paths.update(
        path
        for declaration in declarations
        for path in declaration.extra_evaluation_files(root)
    )
    receipt = CorpusReceipt(
        1,
        ";".join(declaration.selection_description for declaration in declarations),
        True,
        tuple(
            FileChecksum(path.name, sha256(path), path.stat().st_size)
            for path in sorted((root / "archives").iterdir())
            if path.is_file()
        ),
        fields,
        tuple(
            FileChecksum(str(path.relative_to(root)), sha256(path))
            for path in sorted(annotation_paths)
        ),
    )
    (root / "manifest.json").write_text(
        json.dumps(to_jsonable(receipt), indent=2) + "\n"
    )
    return receipt


@dataclass(frozen=True)
class CorpusAudit:
    fields: int
    input_channels: int
    annotation_files: int
    original_archives: int
    colored_registration_pixels: int
    manifest_sha256: str


def audit(root: Path) -> CorpusAudit:
    """Read-only re-verification of frozen identities, pairing and conversions."""
    receipt = TypeAdapter(CorpusReceipt).validate_json(
        (root / "manifest.json").read_text()
    )
    for archive in receipt.archives:
        if sha256(root / "archives" / archive.filename) != archive.sha256:
            raise ValueError(f"Archive checksum mismatch: {archive.filename}")
    for annotation in receipt.annotation_files:
        if sha256(root / annotation.filename) != annotation.sha256:
            raise ValueError(f"Annotation checksum mismatch: {annotation.filename}")
    expected = {
        (field.dataset, field.partition, field.field_id): field
        for field in receipt.fields
    }
    seen = set()
    channels, colored = 0, 0
    for declaration_type in DatasetDeclaration.__registry__.values():
        declaration = declaration_type()
        selections = declaration.selections(root)
        try:
            for selected in selections:
                key = declaration.dataset_id, selected.partition, selected.field_id
                field = expected[key]
                seen.add(key)
                if (
                    field.reference_identity != selected.reference_identity
                    or field.task is not declaration.task
                ):
                    raise ValueError(f"Reference/task identity mismatch: {key}")
                for source, stored in zip(
                    selected.channels, field.channels, strict=True
                ):
                    payload, image = decode_source(source)
                    pixels = declaration.normalize(image, source.member)
                    channels += 1
                    colored += pixels.colored_registration_pixels
                    if (
                        stored.original_member != source.member
                        or stored.identity != source.identity
                        or stored.source_sha256 != hashlib.sha256(payload).hexdigest()
                    ):
                        raise ValueError(f"Source binding mismatch: {stored.filename}")
                    actual = read_labels(root / stored.filename)
                    if (
                        not np.array_equal(actual, pixels.image)
                        or sha256(root / stored.filename) != stored.file_sha256
                        or stored.pixel_sha256
                        != hashlib.sha256(pixels.image.tobytes()).hexdigest()
                    ):
                        raise ValueError(
                            f"Pixel/file identity mismatch: {stored.filename}"
                        )
                    if (
                        stored.conversion is not pixels.conversion
                        or stored.colored_registration_pixels
                        != pixels.colored_registration_pixels
                    ):
                        raise ValueError(
                            f"Conversion receipt mismatch: {stored.filename}"
                        )
                    if tuple(stored.shape) != pixels.image.shape or stored.dtype != str(
                        pixels.image.dtype
                    ):
                        raise ValueError(
                            f"Pixel representation mismatch: {stored.filename}"
                        )
                for source, stored in zip(
                    selected.annotations, field.annotations, strict=True
                ):
                    path = root / stored
                    if (
                        sha256(path)
                        != hashlib.sha256(
                            source.archive.read(source.member)
                        ).hexdigest()
                    ):
                        raise ValueError(
                            f"Annotation source binding mismatch: {stored}"
                        )
                    if declaration.annotation_shape(path) != field.channels[0].shape:
                        raise ValueError(
                            f"Annotation/image coordinate mismatch: {stored}"
                        )
        finally:
            selections.close()
    if seen != set(expected):
        raise ValueError("Incomplete dataset identity coverage")
    return CorpusAudit(
        len(receipt.fields),
        channels,
        len(receipt.annotation_files),
        len(receipt.archives),
        colored,
        sha256(root / "manifest.json"),
    )


def read_labels(path: Path) -> np.ndarray:
    payload = np.asarray(
        FileManager({Backend.DISK.value: DiskStorageBackend()}).load(
            path, Backend.DISK.value
        )
    )
    labels = np.squeeze(payload)
    if labels.ndim != 2 or labels.dtype.kind not in "bui" or np.any(labels < 0):
        raise ValueError(
            f"Not a scalar nonnegative XY integer label map: {path}: {payload.shape}/{payload.dtype}"
        )
    return labels.astype(np.int64, copy=False)


def decode_039(path: Path) -> np.ndarray:
    """Official decoder: first PNG channel, equal-valued connected components.

    https://gist.github.com/jccaicedo/15e811722fca51e3ae90e8b43057f075
    Connected equal-valued regions remain separate when the same color is reused.
    """
    mask = iio.imread(path)
    return label(mask[:, :, 0], connectivity=2, background=0)


def instance_score(
    prediction: np.ndarray, truth: np.ndarray, iou_threshold: float = 0.5
) -> InstanceMetrics:
    if prediction.shape != truth.shape:
        raise ValueError(
            f"Spatial identity mismatch: {prediction.shape} != {truth.shape}"
        )
    # Reserve zero even when a label map entirely lacks background.
    p = np.searchsorted(np.unique(np.r_[0, prediction.ravel()]), prediction.ravel())
    t = np.searchsorted(np.unique(np.r_[0, truth.ravel()]), truth.ravel())
    n_p, n_t = int(p.max()), int(t.max())
    joint = np.bincount(t * (n_p + 1) + p, minlength=(n_t + 1) * (n_p + 1)).reshape(
        n_t + 1, n_p + 1
    )
    intersection = joint[1:, 1:]
    union = joint.sum(axis=1)[1:, None] + joint.sum(axis=0)[None, 1:] - intersection
    iou = np.divide(
        intersection,
        union,
        out=np.zeros_like(intersection, dtype=float),
        where=union > 0,
    )
    # Prioritize maximum cardinality of threshold-valid matches; IoU breaks ties.
    ti, pi = linear_sum_assignment(
        (iou >= iou_threshold).astype(float) + iou / (max(n_p, n_t, 1) + 1),
        maximize=True,
    )
    matched = int(np.count_nonzero(iou[ti, pi] >= iou_threshold))
    overlap_t = np.divide(
        intersection,
        joint.sum(axis=1)[1:, None],
        out=np.zeros_like(intersection, dtype=float),
        where=joint.sum(axis=1)[1:, None] > 0,
    )
    overlap_p = np.divide(
        intersection,
        joint.sum(axis=0)[None, 1:],
        out=np.zeros_like(intersection, dtype=float),
        where=joint.sum(axis=0)[None, 1:] > 0,
    )
    fg_p, fg_t = prediction > 0, truth > 0
    denom = int(fg_p.sum() + fg_t.sum())
    return InstanceMetrics(
        iou_threshold,
        n_t,
        n_p,
        matched,
        n_p - matched,
        n_t - matched,
        matched / n_p if n_p else None,
        matched / n_t if n_t else None,
        2 * matched / (n_p + n_t) if n_p + n_t else 1.0,
        2 * int(np.count_nonzero(fg_p & fg_t)) / denom if denom else 1.0,
        int(np.count_nonzero((overlap_t >= 0.1).sum(axis=1) >= 2)),
        int(np.count_nonzero((overlap_p >= 0.1).sum(axis=0) >= 2)),
        n_p - n_t,
    )


def closed_outline_interiors(outlines: np.ndarray) -> tuple[np.ndarray, int]:
    """Do not bridge open contours; exclude every component meeting the frame."""
    components, _ = ndimage.label(
        ~outlines.astype(bool), structure=ndimage.generate_binary_structure(2, 1)
    )
    border = np.unique(
        np.r_[components[0], components[-1], components[:, 0], components[:, -1]]
    )
    components[np.isin(components, border)] = 0
    closed = label(components, connectivity=1, background=0)
    return closed, len(border) - (0 in border)


def boundary_score_007(
    prediction: np.ndarray, manual_outlines: np.ndarray
) -> BoundaryMetrics:
    """Published directed metric: adjacent-cell boundaries, distance<=2pixels.

    Internal four-neighbor label transitions define predicted boundary pixels.
    Exclude pixels adjacent (eight neighbors) to background or the image edge.
    Distance is to the union of manual outlines; object correspondence is not
    identifiable from monochrome outlines, so this limitation is explicit.
    https://bbbc.broadinstitute.org/BBBC007
    """
    if prediction.shape != manual_outlines.shape:
        raise ValueError("Cell label and manual outline shapes differ")
    if not np.any(manual_outlines):
        raise ValueError("Manual cell outlines are empty")
    boundary = np.zeros(prediction.shape, dtype=bool)
    for axis in (0, 1):
        left, right = [slice(None)] * 2, [slice(None)] * 2
        left[axis], right[axis] = slice(None, -1), slice(1, None)
        left, right = tuple(left), tuple(right)
        differing = (
            (prediction[left] != prediction[right])
            & (prediction[left] > 0)
            & (prediction[right] > 0)
        )
        boundary[left] |= differing
        boundary[right] |= differing
    relevant = boundary & ndimage.binary_erosion(
        prediction > 0, structure=np.ones((3, 3)), border_value=0
    )
    distances = ndimage.distance_transform_edt(~manual_outlines.astype(bool))
    total = int(relevant.sum())
    return BoundaryMetrics(
        total,
        int(np.count_nonzero(relevant & (distances <= 2))),
        float(np.mean(distances[relevant] <= 2)) if total else None,
    )


def score_039(prediction: Path, annotation: Path) -> NuclearFieldScore:
    return NuclearFieldScore(
        FileChecksum(str(prediction), sha256(prediction)),
        FileChecksum(str(annotation), sha256(annotation)),
        instance_score(read_labels(prediction), decode_039(annotation)),
    )


def summarize_nuclear_partition(
    fields: tuple[NuclearFieldScore, ...],
) -> NuclearPartitionMetrics:
    if not fields:
        raise ValueError("Cannot summarize an empty nuclear partition")
    metrics = tuple(field.metrics for field in fields)
    true_instances = sum(metric.true_instances for metric in metrics)
    predicted_instances = sum(metric.predicted_instances for metric in metrics)
    matched = sum(metric.matched for metric in metrics)
    denominator = true_instances + predicted_instances
    return NuclearPartitionMetrics(
        fields=len(fields),
        true_instances=true_instances,
        predicted_instances=predicted_instances,
        matched=matched,
        false_positive=sum(metric.false_positive for metric in metrics),
        false_negative=sum(metric.false_negative for metric in metrics),
        precision=matched / predicted_instances if predicted_instances else None,
        recall=matched / true_instances if true_instances else None,
        object_f1=2 * matched / denominator if denominator else 1.0,
        mean_field_object_f1=float(np.mean([metric.object_f1 for metric in metrics])),
        mean_field_pixel_dice=float(np.mean([metric.pixel_dice for metric in metrics])),
        split_truth_instances_overlap_ge_10pct=sum(
            metric.split_truth_instances_overlap_ge_10pct for metric in metrics
        ),
        merged_predicted_instances_overlap_ge_10pct=sum(
            metric.merged_predicted_instances_overlap_ge_10pct for metric in metrics
        ),
        count_error=predicted_instances - true_instances,
    )


def score_039_partition(
    corpus_root: Path,
    trial_root: Path,
    prediction_manifest: Path,
    partition: Partition,
) -> NuclearPartitionScore:
    """Score one frozen BBBC039 partition after authoring access has ended."""
    corpus_manifest = corpus_root / "manifest.json"
    receipt = TypeAdapter(CorpusReceipt).validate_json(corpus_manifest.read_text())
    frozen = FrozenPredictionSet.from_sha256sum(trial_root, prediction_manifest)
    fields = tuple(
        score_039(
            frozen.unique_source_artifact(field.channels[0].filename, ".labels.tif"),
            corpus_root / field.annotations[0],
        )
        for field in receipt.fields
        if field.dataset is DatasetId.NUCLEI_039 and field.partition is partition
    )
    return NuclearPartitionScore(
        dataset=DatasetId.NUCLEI_039,
        partition=partition,
        corpus_manifest=FileChecksum(
            str(corpus_manifest),
            sha256(corpus_manifest),
            corpus_manifest.stat().st_size,
        ),
        prediction_manifest=frozen.manifest,
        fields=fields,
        metrics=summarize_nuclear_partition(fields),
    )


def score_007(
    nuclei_prediction: Path,
    cells_prediction: Path,
    nuclei_outline: Path,
    cells_outline: Path,
) -> CellFieldScore:
    nuclei, cells = read_labels(nuclei_prediction), read_labels(cells_prediction)
    nuclear_truth, excluded = closed_outline_interiors(read_labels(nuclei_outline))
    outlines = read_labels(cells_outline)
    if nuclei.shape != cells.shape or nuclei.shape != nuclear_truth.shape:
        raise ValueError("Nuclear/cell spatial identities differ")
    associations = []
    for nucleus in np.unique(nuclei[nuclei > 0]):
        values, counts = np.unique(cells[nuclei == nucleus], return_counts=True)
        present = values > 0
        associations.append(
            int(values[present][np.argmax(counts[present])]) if present.any() else 0
        )
    nonzero = [c for c in associations if c > 0]
    return CellFieldScore(
        FileChecksum(str(nuclei_prediction), sha256(nuclei_prediction)),
        FileChecksum(str(cells_prediction), sha256(cells_prediction)),
        int(nuclear_truth.max()),
        excluded,
        len(associations) - int(nuclear_truth.max()),
        int(np.unique(cells[cells > 0]).size),
        len(associations),
        associations.count(0),
        len(nonzero) - len(set(nonzero)),
        boundary_score_007(cells, outlines),
    )


def summarize_cell_partition(
    fields: tuple[CellFieldScore, ...],
) -> CellPartitionMetrics:
    if not fields:
        raise ValueError("Cannot summarize an empty cell partition")
    boundary_fractions = tuple(
        field.boundary.adjacent_boundary_within_2px_fraction
        for field in fields
        if field.boundary.adjacent_boundary_within_2px_fraction is not None
    )
    relevant_boundary_pixels = sum(
        field.boundary.relevant_boundary_pixels for field in fields
    )
    boundary_pixels_within_2px = sum(field.boundary.within_2px for field in fields)
    return CellPartitionMetrics(
        fields=len(fields),
        manual_nucleus_closed_interiors=sum(
            field.manual_nucleus_closed_interiors for field in fields
        ),
        manual_nucleus_frame_or_open_regions_excluded=sum(
            field.manual_nucleus_frame_or_open_regions_excluded for field in fields
        ),
        predicted_nucleus_count=sum(field.predicted_nucleus_count for field in fields),
        nuclear_count_error_vs_closed_interiors=sum(
            field.nuclear_count_error_vs_closed_interiors for field in fields
        ),
        predicted_cell_count=sum(field.predicted_cell_count for field in fields),
        nuclei_without_cell_overlap=sum(
            field.nuclei_without_cell_overlap for field in fields
        ),
        extra_nuclei_sharing_a_predicted_cell=sum(
            field.extra_nuclei_sharing_a_predicted_cell for field in fields
        ),
        relevant_boundary_pixels=relevant_boundary_pixels,
        boundary_pixels_within_2px=boundary_pixels_within_2px,
        pooled_adjacent_boundary_within_2px_fraction=(
            boundary_pixels_within_2px / relevant_boundary_pixels
            if relevant_boundary_pixels
            else None
        ),
        mean_field_adjacent_boundary_within_2px_fraction=(
            float(np.mean(boundary_fractions)) if boundary_fractions else None
        ),
    )


def score_007_partition(
    corpus_root: Path,
    trial_root: Path,
    prediction_manifest: Path,
    partition: Partition,
) -> CellPartitionScore:
    """Score one frozen BBBC007 partition after authoring access has ended."""
    corpus_manifest = corpus_root / "manifest.json"
    receipt = TypeAdapter(CorpusReceipt).validate_json(corpus_manifest.read_text())
    frozen = FrozenPredictionSet.from_sha256sum(trial_root, prediction_manifest)
    fields = tuple(
        score_007(
            frozen.unique_component_artifact(
                field.field_id,
                1,
                ".labels.tif",
            ),
            frozen.unique_component_artifact(
                field.field_id,
                2,
                ".labels.tif",
            ),
            corpus_root / field.annotations[0],
            corpus_root / field.annotations[1],
        )
        for field in receipt.fields
        if field.dataset is DatasetId.CELLS_007 and field.partition is partition
    )
    return CellPartitionScore(
        dataset=DatasetId.CELLS_007,
        partition=partition,
        corpus_manifest=FileChecksum(
            str(corpus_manifest),
            sha256(corpus_manifest),
            corpus_manifest.stat().st_size,
        ),
        prediction_manifest=frozen.manifest,
        fields=fields,
        metrics=summarize_cell_partition(fields),
    )


@dataclass(frozen=True)
class DoseResponsePoint:
    well: str
    dose: float
    unit: str
    mean_nuclear_cytoplasmic_gfp_ratio: float


@dataclass(frozen=True)
class TreatmentMetrics:
    treatment: Treatment
    positive_n: int
    negative_n: int
    dose_response: tuple[DoseResponsePoint, ...]
    z_prime: float | None
    positive_mean: float | None
    negative_mean: float | None


@dataclass(frozen=True)
class TranslocationMetrics:
    treatments: tuple[TreatmentMetrics, ...]
    measurement_definition: str = (
        "per-well mean of cell-level mean nuclear GFP / mean cytoplasmic GFP; sampleSD across wells; distinct treatment groups"
    )
    segmentation_truth: bool = False


@dataclass(frozen=True)
class TranslocationWellScore:
    well: str
    cells: int
    mean_nuclear_cytoplasmic_gfp_ratio: float
    measurement: FileChecksum


@dataclass(frozen=True)
class TranslocationPartitionScore:
    dataset: DatasetId
    partition: Partition
    corpus_manifest: FileChecksum
    prediction_manifest: FileChecksum
    nuclear_object_name: str
    cytoplasmic_object_name: str
    source_image_name: str
    wells: tuple[TranslocationWellScore, ...]
    metrics: TranslocationMetrics


def _translocation_measurement_artifact(
    frozen: FrozenPredictionSet,
    well: str,
    *,
    required_fields: frozenset[str],
) -> Path:
    """Resolve the one frozen well table carrying the declared endpoint fields."""

    candidates = []
    for artifact in frozen.artifacts:
        path = frozen.root / artifact.filename
        if not Path(artifact.filename).name.startswith(f"{well}_"):
            continue
        if path.suffix.lower() != ".csv":
            continue
        with path.open(newline="") as handle:
            fields = frozenset(csv.DictReader(handle).fieldnames or ())
        if required_fields <= fields:
            candidates.append(path)
    if len(candidates) != 1:
        raise ValueError(
            f"Expected one endpoint measurement table for {well}; "
            f"found {[path.name for path in candidates]!r}."
        )
    return candidates[0]


def score_translocation_well_013(
    frozen: FrozenPredictionSet,
    well: str,
    *,
    nuclear_object_name: str,
    cytoplasmic_object_name: str,
    source_image_name: str,
) -> TranslocationWellScore:
    """Compute the declared cell-paired BBBC013 endpoint for one frozen well."""

    object_name_field = MeasurementRowAxisField.OBJECT_NAME.value
    object_label_field = MeasurementRowAxisField.OBJECT_LABEL.value
    intensity_field = MeasureObjectIntensityModule.MeasurementFeature.MEAN_INTENSITY.source_qualified_name(
        source_image_name
    )
    path = _translocation_measurement_artifact(
        frozen,
        well,
        required_fields=frozenset(
            (object_name_field, object_label_field, intensity_field)
        ),
    )
    values_by_subject: dict[str, dict[int, float]] = {
        nuclear_object_name: {},
        cytoplasmic_object_name: {},
    }
    with path.open(newline="") as handle:
        for row in csv.DictReader(handle):
            object_name = row[object_name_field]
            if object_name not in values_by_subject:
                continue
            object_label = int(row[object_label_field])
            subject_values = values_by_subject[object_name]
            if object_label in subject_values:
                raise ValueError(
                    f"Duplicate {object_name} object label {object_label} in {path}."
                )
            subject_values[object_label] = float(row[intensity_field])
    nuclear = values_by_subject[nuclear_object_name]
    cytoplasmic = values_by_subject[cytoplasmic_object_name]
    if not nuclear or nuclear.keys() != cytoplasmic.keys():
        raise ValueError(
            f"Well {well} does not carry one matched nuclear/cytoplasmic object "
            f"domain: nuclear={len(nuclear)}, cytoplasmic={len(cytoplasmic)}."
        )
    zero_denominators = tuple(
        object_label
        for object_label, intensity in cytoplasmic.items()
        if intensity == 0
    )
    if zero_denominators:
        raise ValueError(
            f"Well {well} has zero cytoplasmic mean intensity for object labels "
            f"{zero_denominators!r}."
        )
    ratios = tuple(
        nuclear[object_label] / cytoplasmic[object_label] for object_label in nuclear
    )
    return TranslocationWellScore(
        well=well,
        cells=len(ratios),
        mean_nuclear_cytoplasmic_gfp_ratio=float(np.mean(ratios)),
        measurement=FileChecksum(str(path), sha256(path), path.stat().st_size),
    )


def score_013_partition(
    corpus_root: Path,
    trial_root: Path,
    prediction_manifest: Path,
    partition: Partition,
    *,
    nuclear_object_name: str,
    cytoplasmic_object_name: str,
    source_image_name: str,
) -> TranslocationPartitionScore:
    """Score one frozen BBBC013 partition from matched per-cell measurements."""

    corpus_manifest = corpus_root / "manifest.json"
    receipt = TypeAdapter(CorpusReceipt).validate_json(corpus_manifest.read_text())
    plate_map_path = (
        corpus_root
        / "evaluation"
        / DatasetId.TRANSLOCATION_013.value
        / "plate_map.json"
    )
    plate_map = TypeAdapter(tuple[PlateWell, ...]).validate_json(
        plate_map_path.read_text()
    )
    frozen = FrozenPredictionSet.from_sha256sum(trial_root, prediction_manifest)
    wells = tuple(
        score_translocation_well_013(
            frozen,
            field.field_id,
            nuclear_object_name=nuclear_object_name,
            cytoplasmic_object_name=cytoplasmic_object_name,
            source_image_name=source_image_name,
        )
        for field in receipt.fields
        if field.dataset is DatasetId.TRANSLOCATION_013 and field.partition is partition
    )
    well_measurements = {
        well.well: well.mean_nuclear_cytoplasmic_gfp_ratio for well in wells
    }
    return TranslocationPartitionScore(
        dataset=DatasetId.TRANSLOCATION_013,
        partition=partition,
        corpus_manifest=FileChecksum(
            str(corpus_manifest),
            sha256(corpus_manifest),
            corpus_manifest.stat().st_size,
        ),
        prediction_manifest=frozen.manifest,
        nuclear_object_name=nuclear_object_name,
        cytoplasmic_object_name=cytoplasmic_object_name,
        source_image_name=source_image_name,
        wells=wells,
        metrics=control_score_013(well_measurements, plate_map),
    )


def control_score_013(
    well_measurements: dict[str, float], plate_map: tuple[PlateWell, ...]
) -> TranslocationMetrics:
    """Assay endpoint with wells, not cells, as independent replicates.

    Values must be per-well means of cell-level nuclear/cytoplasmicGFP ratios.
    This evaluator does not claim that segmentation has manual truth or that a
    numeric disagreement with publishedZ' identifies an implementation error.
    """
    results = []
    for treatment in Treatment:
        positive, negative, response = [], [], []
        for record in plate_map:
            if (
                record.treatment is not treatment
                or record.well not in well_measurements
            ):
                continue
            value = well_measurements[record.well]
            if not np.isfinite(value):
                raise ValueError("Nonfinite well measurement")
            if record.role is PlateRole.POSITIVE:
                positive.append(value)
            elif record.role is PlateRole.NEGATIVE:
                negative.append(value)
            elif record.role is PlateRole.DOSE:
                response.append(
                    DoseResponsePoint(record.well, record.dose, record.unit, value)
                )
        z_prime, positive_mean, negative_mean = None, None, None
        if len(positive) >= 2 and len(negative) >= 2:
            positive_mean, negative_mean = float(np.mean(positive)), float(
                np.mean(negative)
            )
            separation = abs(positive_mean - negative_mean)
            z_prime = (
                1
                - 3
                * float(np.std(positive, ddof=1) + np.std(negative, ddof=1))
                / separation
                if separation
                else None
            )
        results.append(
            TreatmentMetrics(
                treatment,
                len(positive),
                len(negative),
                tuple(response),
                z_prime,
                positive_mean,
                negative_mean,
            )
        )
    return TranslocationMetrics(tuple(results))


@dataclass(frozen=True)
class PreparationSummary:
    fields: int
    manifest: Path


def prepare_command(args: argparse.Namespace) -> PreparationSummary:
    result = prepare(args.root)
    return PreparationSummary(len(result.fields), args.root / "manifest.json")


def audit_command(args: argparse.Namespace) -> CorpusAudit:
    return audit(args.root)


def nuclei_command(args: argparse.Namespace) -> NuclearFieldScore:
    return score_039(args.prediction, args.annotation)


def cells_command(args: argparse.Namespace) -> CellFieldScore:
    return score_007(
        args.nuclei_prediction,
        args.cells_prediction,
        args.nuclei_outline,
        args.cells_outline,
    )


def cells_partition_command(args: argparse.Namespace) -> CellPartitionScore:
    return score_007_partition(
        args.corpus_root,
        args.trial_root,
        args.prediction_manifest,
        args.partition,
    )


def translocation_partition_command(
    args: argparse.Namespace,
) -> TranslocationPartitionScore:
    return score_013_partition(
        args.corpus_root,
        args.trial_root,
        args.prediction_manifest,
        args.partition,
        nuclear_object_name=args.nuclear_object_name,
        cytoplasmic_object_name=args.cytoplasmic_object_name,
        source_image_name=args.source_image_name,
    )


def nuclei_partition_command(args: argparse.Namespace) -> NuclearPartitionScore:
    return score_039_partition(
        args.corpus_root,
        args.trial_root,
        args.prediction_manifest,
        args.partition,
    )


def freeze_command(args: argparse.Namespace) -> PredictionFreezeReceipt:
    return freeze_prediction_directory(
        args.root,
        args.prediction_directory,
        args.manifest,
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        help="Write the typed JSON receipt in addition to stdout.",
    )
    sub = parser.add_subparsers(required=True)
    prep = sub.add_parser("prepare")
    prep.add_argument("root", type=Path)
    prep.set_defaults(action=prepare_command)
    check = sub.add_parser("audit")
    check.add_argument("root", type=Path)
    check.set_defaults(action=audit_command)
    scoring = sub.add_parser("score039")
    scoring.add_argument("prediction", type=Path)
    scoring.add_argument("annotation", type=Path)
    scoring.set_defaults(action=nuclei_command)
    partition_scoring = sub.add_parser("score039-partition")
    partition_scoring.add_argument("corpus_root", type=Path)
    partition_scoring.add_argument("trial_root", type=Path)
    partition_scoring.add_argument("prediction_manifest", type=Path)
    partition_scoring.add_argument(
        "partition", type=Partition, choices=tuple(Partition)
    )
    partition_scoring.set_defaults(action=nuclei_partition_command)
    freeze = sub.add_parser("freeze-predictions")
    freeze.add_argument("root", type=Path)
    freeze.add_argument("prediction_directory", type=Path)
    freeze.add_argument("manifest", type=Path)
    freeze.set_defaults(action=freeze_command)
    cell = sub.add_parser("score007")
    for name in (
        "nuclei_prediction",
        "cells_prediction",
        "nuclei_outline",
        "cells_outline",
    ):
        cell.add_argument(name, type=Path)
    cell.set_defaults(action=cells_command)
    cell_partition = sub.add_parser("score007-partition")
    cell_partition.add_argument("corpus_root", type=Path)
    cell_partition.add_argument("trial_root", type=Path)
    cell_partition.add_argument("prediction_manifest", type=Path)
    cell_partition.add_argument("partition", type=Partition, choices=tuple(Partition))
    cell_partition.set_defaults(action=cells_partition_command)
    translocation_partition = sub.add_parser("score013-partition")
    translocation_partition.add_argument("corpus_root", type=Path)
    translocation_partition.add_argument("trial_root", type=Path)
    translocation_partition.add_argument("prediction_manifest", type=Path)
    translocation_partition.add_argument(
        "partition", type=Partition, choices=tuple(Partition)
    )
    translocation_partition.add_argument("nuclear_object_name")
    translocation_partition.add_argument("cytoplasmic_object_name")
    translocation_partition.add_argument("source_image_name")
    translocation_partition.set_defaults(action=translocation_partition_command)
    args = parser.parse_args()
    serialized = json.dumps(to_jsonable(args.action(args)), indent=2) + "\n"
    if args.output is not None:
        args.output.write_text(serialized)
    print(serialized, end="")


if __name__ == "__main__":
    main()
