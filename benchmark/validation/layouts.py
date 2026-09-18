"""Registered source-layout normalizers for independent validation datasets."""

from __future__ import annotations

import csv
import re
from abc import ABC, abstractmethod
from pathlib import Path
from typing import ClassVar

from metaclass_registry import AutoRegisterMeta

from benchmark.contracts.validation import (
    IndependentValidationSpec,
    ValidationAssayRole,
    ValidationDatasetLayout,
    ValidationImageRecord,
    ValidationPartition,
    ValidationReferenceRecord,
)


class ValidationCorpusLayoutError(ValueError):
    """Raised when acquired data contradicts its declared validation layout."""


class ValidationCorpusLayoutStrategy(ABC, metaclass=AutoRegisterMeta):
    """Normalize one declared upstream layout into common authoring records."""

    __registry_key__ = "layout_key"
    __skip_if_no_key__ = True
    layout_key: ClassVar[ValidationDatasetLayout | None] = None

    @classmethod
    def for_layout(
        cls,
        layout: ValidationDatasetLayout,
    ) -> ValidationCorpusLayoutStrategy:
        try:
            strategy_type = cls.__registry__[layout]
        except KeyError as exc:
            raise ValidationCorpusLayoutError(
                f"No validation layout strategy is registered for {layout.value!r}."
            ) from exc
        return strategy_type()

    @abstractmethod
    def normalize(
        self,
        raw_root: Path,
        validation: IndependentValidationSpec,
    ) -> tuple[
        tuple[ValidationImageRecord, ...], tuple[ValidationReferenceRecord, ...]
    ]:
        """Return authoring images and scoring-only references."""


def _unique_directory(raw_root: Path, name: str) -> Path:
    matches = tuple(
        path
        for path in raw_root.rglob(name)
        if path.is_dir() and "__MACOSX" not in path.parts
    )
    if len(matches) != 1:
        raise ValidationCorpusLayoutError(
            f"Expected one {name!r} directory under {raw_root}, found {matches!r}."
        )
    return matches[0]


def _unique_file(raw_root: Path, name: str) -> Path:
    matches = tuple(
        path
        for path in raw_root.rglob(name)
        if path.is_file() and "__MACOSX" not in path.parts
    )
    if len(matches) != 1:
        raise ValidationCorpusLayoutError(
            f"Expected one {name!r} file under {raw_root}, found {matches!r}."
        )
    return matches[0]


class PartitionedInstanceMaskLayout(ValidationCorpusLayoutStrategy):
    """Normalize BBBC039 images, official partitions, and colour masks."""

    layout_key = ValidationDatasetLayout.PARTITIONED_INSTANCE_MASKS
    _IMAGE_PATTERN = re.compile(r"^IXMtest_(?P<well>[A-P]\d{2})_s(?P<site>\d+)_w1.+$")

    def normalize(
        self,
        raw_root: Path,
        validation: IndependentValidationSpec,
    ) -> tuple[
        tuple[ValidationImageRecord, ...], tuple[ValidationReferenceRecord, ...]
    ]:
        images_root = _unique_directory(raw_root, "images")
        masks_root = _unique_directory(raw_root, "masks")
        metadata_root = _unique_directory(raw_root, "metadata")
        partitions = self._partition_by_stem(metadata_root)
        plates = self._plate_by_stem(metadata_root)
        mask_by_stem = {
            path.stem: path for path in masks_root.glob("*.png") if path.is_file()
        }

        records: list[ValidationImageRecord] = []
        references: list[ValidationReferenceRecord] = []
        for image_path in sorted(images_root.glob("*.tif")):
            match = self._IMAGE_PATTERN.fullmatch(image_path.stem)
            if match is None:
                raise ValidationCorpusLayoutError(
                    f"Unrecognized BBBC039 image name: {image_path.name}"
                )
            partition = partitions.get(image_path.stem)
            plate = plates.get(image_path.stem)
            mask_path = mask_by_stem.get(image_path.stem)
            if partition is None or plate is None or mask_path is None:
                raise ValidationCorpusLayoutError(
                    f"BBBC039 image {image_path.name!r} lacks partition or mask."
                )
            well = match.group("well")
            site = match.group("site")
            source_set_id = f"{plate}_{well}_{site}"
            canonical_name = f"plate-{plate}_well-{well}_site-{site}_channel-DNA.tif"
            records.append(
                ValidationImageRecord(
                    source_relative_path=image_path.relative_to(raw_root),
                    canonical_relative_path=Path("images")
                    / partition.value
                    / canonical_name,
                    source_set_id=source_set_id,
                    selection_key=image_path.name,
                    partition=partition,
                    well=well,
                    site=site,
                    channel="DNA",
                    metadata=(("plate", plate),),
                )
            )
            references.append(
                ValidationReferenceRecord(
                    source_relative_path=mask_path.relative_to(raw_root),
                    canonical_relative_path=(
                        Path("references")
                        / partition.value
                        / f"{source_set_id}_channel-DNA.npz"
                    ),
                    source_set_id=source_set_id,
                    reference_kind=validation.evidence_kind,
                    partition=partition,
                    channel="DNA",
                )
            )

        if len(records) != validation.expected_input_planes:
            raise ValidationCorpusLayoutError(
                f"BBBC039 produced {len(records)} input planes; "
                f"expected {validation.expected_input_planes}."
            )
        return tuple(records), tuple(references)

    @staticmethod
    def _plate_by_stem(metadata_root: Path) -> dict[str, str]:
        mapping: dict[str, str] = {}
        with (metadata_root / "filenames_and_plates.csv").open(
            newline="", encoding="utf-8-sig"
        ) as handle:
            for filename, plate in csv.reader(handle):
                stem = Path(filename).stem
                if stem in mapping:
                    raise ValidationCorpusLayoutError(
                        f"BBBC039 source {stem!r} has duplicate plate metadata."
                    )
                mapping[stem] = plate
        if len(mapping) != 200:
            raise ValidationCorpusLayoutError(
                f"BBBC039 plate metadata contains {len(mapping)} images, expected 200."
            )
        return mapping

    @staticmethod
    def _partition_by_stem(metadata_root: Path) -> dict[str, ValidationPartition]:
        mapping: dict[str, ValidationPartition] = {}
        declarations = (
            ("training.txt", ValidationPartition.TRAINING),
            ("validation.txt", ValidationPartition.VALIDATION),
            ("test.txt", ValidationPartition.TEST),
        )
        for filename, partition in declarations:
            for line in (
                (metadata_root / filename).read_text(encoding="utf-8").splitlines()
            ):
                stem = Path(line.strip()).stem
                if not stem:
                    continue
                if stem in mapping:
                    raise ValidationCorpusLayoutError(
                        f"BBBC039 source {stem!r} occurs in multiple partitions."
                    )
                mapping[stem] = partition
        if len(mapping) != 200:
            raise ValidationCorpusLayoutError(
                f"BBBC039 partition metadata contains {len(mapping)} images, expected 200."
            )
        return mapping


class PairedManualOutlinesLayout(ValidationCorpusLayoutStrategy):
    """Normalize BBBC007 paired DNA/actin planes and complete manual outlines."""

    layout_key = ValidationDatasetLayout.PAIRED_MANUAL_OUTLINES

    def normalize(
        self,
        raw_root: Path,
        validation: IndependentValidationSpec,
    ) -> tuple[
        tuple[ValidationImageRecord, ...], tuple[ValidationReferenceRecord, ...]
    ]:
        images_root = _unique_directory(raw_root, "BBBC007_v1_images")
        outlines_root = _unique_directory(raw_root, "BBBC007_v1_outlines")
        group_wells = {
            group_name: f"A{index:02d}"
            for index, group_name in enumerate(
                sorted(path.name for path in images_root.iterdir() if path.is_dir()),
                start=1,
            )
        }
        records: list[ValidationImageRecord] = []
        references: list[ValidationReferenceRecord] = []
        seen_planes: set[tuple[str, str, str]] = set()
        image_paths = tuple(sorted(images_root.rglob("*.tif")))
        selection_key_by_pair = {
            pair_key: image_path.name
            for image_path in image_paths
            for pair_key, _, channel in (
                (self._plane_identity(image_path.relative_to(images_root))),
            )
            if channel == "DNA"
        }

        for image_path in image_paths:
            relative = image_path.relative_to(images_root)
            pair_key, site, channel = self._plane_identity(relative)
            well = group_wells[relative.parts[0]]
            plane_identity = (well, site, channel)
            if plane_identity in seen_planes:
                raise ValidationCorpusLayoutError(
                    f"Duplicate BBBC007 normalized plane {plane_identity!r}."
                )
            seen_planes.add(plane_identity)
            canonical_name = f"well-{well}_site-{site}_channel-{channel}.tif"
            records.append(
                ValidationImageRecord(
                    source_relative_path=image_path.relative_to(raw_root),
                    canonical_relative_path=Path("images") / canonical_name,
                    source_set_id=f"{well}_{site}",
                    selection_key=selection_key_by_pair[pair_key],
                    partition=ValidationPartition.COMPLETE,
                    well=well,
                    site=site,
                    channel=channel,
                    metadata=(("official_pair_key", pair_key),),
                )
            )
            outline_path = outlines_root / relative
            if not outline_path.is_file():
                raise ValidationCorpusLayoutError(
                    f"BBBC007 image {relative!s} has no corresponding manual outline."
                )
            references.append(
                ValidationReferenceRecord(
                    source_relative_path=outline_path.relative_to(raw_root),
                    canonical_relative_path=(
                        Path("references")
                        / ValidationPartition.COMPLETE.value
                        / f"{well}_{site}_channel-{channel}.tif"
                    ),
                    source_set_id=f"{well}_{site}",
                    reference_kind=validation.evidence_kind,
                    partition=ValidationPartition.COMPLETE,
                    channel=channel,
                )
            )

        if len(records) != validation.expected_input_planes:
            raise ValidationCorpusLayoutError(
                f"BBBC007 produced {len(records)} input planes; "
                f"expected {validation.expected_input_planes}."
            )
        pair_counts: dict[tuple[str, str], set[str]] = {}
        for record in records:
            pair_counts.setdefault((record.well, record.site), set()).add(
                record.channel
            )
        incomplete = {
            identity: channels
            for identity, channels in pair_counts.items()
            if channels != {"DNA", "ACTIN"}
        }
        if incomplete:
            raise ValidationCorpusLayoutError(
                f"BBBC007 contains incomplete DNA/actin source sets: {incomplete!r}."
            )
        return tuple(records), tuple(references)

    @staticmethod
    def _plane_identity(relative_path: Path) -> tuple[str, str, str]:
        stem = relative_path.stem
        patterns = (
            (
                re.compile(r"^(?P<base>.+ p(?P<site>\d+))(?P<channel>[df])$"),
                {"d": "DNA", "f": "ACTIN"},
                0,
            ),
            (
                re.compile(r"^(?P<base>.+_POS(?P<site>\d+))_(?P<channel>[DF])_[12]UL$"),
                {"D": "DNA", "F": "ACTIN"},
                0,
            ),
            (
                re.compile(r"^(?P<base>.+f(?P<site>\d+)d)(?P<channel>[01])$"),
                {"0": "DNA", "1": "ACTIN"},
                1,
            ),
        )
        for pattern, channel_by_token, site_offset in patterns:
            match = pattern.fullmatch(stem)
            if match is not None:
                return (
                    f"{relative_path.parent.name}/{match.group('base')}",
                    str(int(match.group("site")) + site_offset),
                    channel_by_token[match.group("channel")],
                )
        raise ValidationCorpusLayoutError(
            f"Unrecognized BBBC007 image naming pattern: {relative_path!s}."
        )


class TranslocationPlateLayout(ValidationCorpusLayoutStrategy):
    """Normalize BBBC013 paired channels and official dose/control metadata."""

    layout_key = ValidationDatasetLayout.TRANSLOCATION_PLATE
    _IMAGE_PATTERN = re.compile(
        r"^Channel(?P<channel>[12])-(?P<ordinal>\d+)-"
        r"(?P<row>[A-H])-(?P<column>\d{2})\.BMP$",
        re.IGNORECASE,
    )

    def normalize(
        self,
        raw_root: Path,
        validation: IndependentValidationSpec,
    ) -> tuple[
        tuple[ValidationImageRecord, ...], tuple[ValidationReferenceRecord, ...]
    ]:
        images_root = _unique_directory(raw_root, "BBBC013_v1_images_bmp")
        metadata = self._well_metadata(raw_root)
        channel_by_token = {"1": "GFP", "2": "DNA"}
        records: list[ValidationImageRecord] = []
        seen: set[tuple[str, str]] = set()
        for image_path in sorted(images_root.glob("*.BMP")):
            match = self._IMAGE_PATTERN.fullmatch(image_path.name)
            if match is None:
                raise ValidationCorpusLayoutError(
                    f"Unrecognized BBBC013 image name: {image_path.name}"
                )
            well = f"{match.group('row').upper()}{int(match.group('column')):02d}"
            channel = channel_by_token[match.group("channel")]
            identity = (well, channel)
            if identity in seen:
                raise ValidationCorpusLayoutError(
                    f"Duplicate BBBC013 normalized plane {identity!r}."
                )
            seen.add(identity)
            well_metadata = metadata.get(well)
            if well_metadata is None:
                raise ValidationCorpusLayoutError(
                    f"BBBC013 well {well!r} is absent from official reproduction metadata."
                )
            canonical_name = f"well-{well}_site-1_channel-{channel}.bmp"
            records.append(
                ValidationImageRecord(
                    source_relative_path=image_path.relative_to(raw_root),
                    canonical_relative_path=Path("images") / canonical_name,
                    source_set_id=f"{well}_1",
                    selection_key=well,
                    partition=ValidationPartition.COMPLETE,
                    well=well,
                    site="1",
                    channel=channel,
                    metadata=tuple(sorted(well_metadata.items())),
                )
            )
        if len(records) != validation.expected_input_planes:
            raise ValidationCorpusLayoutError(
                f"BBBC013 produced {len(records)} input planes; "
                f"expected {validation.expected_input_planes}."
            )
        return tuple(records), ()

    @staticmethod
    def _well_metadata(raw_root: Path) -> dict[str, dict[str, str]]:
        wortmannin_path = _unique_file(
            raw_root,
            "Bioimage_CP2_Dose_WellMetadata_wortmannin.csv",
        )
        ly_path = _unique_file(
            raw_root,
            "Bioimage_CP2_Dose_WellMetadata_LY294002_Corrected_EFGH01_Controls.csv",
        )
        rows: dict[str, dict[str, str]] = {}
        for path, allowed_rows, dose_treatment, dose_unit in (
            (wortmannin_path, frozenset("ABCD"), "Wortmannin", "nM"),
            (ly_path, frozenset("EFGH"), "LY294002", "uM"),
        ):
            with path.open(newline="", encoding="utf-8-sig") as handle:
                for row in csv.DictReader(handle):
                    well_row = row["Metadata_WellRow"].upper()
                    if well_row not in allowed_rows:
                        continue
                    well = row["Metadata_Well"].upper()
                    control_code = float(row["Metadata_PosNegCtrls"])
                    if control_code == 1.0:
                        assay_role = ValidationAssayRole.POSITIVE_CONTROL
                        treatment = "Wortmannin"
                        concentration = "150"
                        unit = "nM"
                    elif control_code == 0.0:
                        assay_role = ValidationAssayRole.NEGATIVE_CONTROL
                        treatment = "vehicle"
                        concentration = "0"
                        unit = dose_unit
                    else:
                        assay_role = (
                            ValidationAssayRole.DOSE
                            if float(row["Metadata_Dose"]) > 0
                            else ValidationAssayRole.EMPTY
                        )
                        treatment = dose_treatment
                        concentration = row["Metadata_Dose"]
                        unit = dose_unit
                    rows[well] = {
                        "assay_block": dose_treatment,
                        "assay_role": assay_role.value,
                        "treatment": treatment,
                        "concentration": concentration,
                        "concentration_unit": unit,
                    }
        if len(rows) != 96:
            raise ValidationCorpusLayoutError(
                f"BBBC013 reproduction metadata yielded {len(rows)} wells, expected 96."
            )
        return rows
