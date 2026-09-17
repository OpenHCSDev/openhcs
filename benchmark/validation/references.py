"""Registered materialization and decoding of trusted validation references."""

from __future__ import annotations

import os
import shutil
from abc import ABC, abstractmethod
from pathlib import Path
from typing import ClassVar

import imageio.v3 as iio
import numpy as np
from metaclass_registry import AutoRegisterMeta
from skimage.measure import label
from skimage.segmentation import relabel_sequential

from benchmark.contracts.validation import (
    ValidationEvidenceKind,
    ValidationReferenceRecord,
)


class ValidationReferenceError(ValueError):
    """Raised when trusted reference material contradicts its declaration."""


class ValidationReferenceStrategy(ABC, metaclass=AutoRegisterMeta):
    """Own materialization and loading for one independent evidence kind."""

    __registry_key__ = "evidence_kind"
    __skip_if_no_key__ = True
    evidence_kind: ClassVar[ValidationEvidenceKind | None] = None

    @classmethod
    def for_evidence(
        cls,
        evidence_kind: ValidationEvidenceKind,
    ) -> ValidationReferenceStrategy:
        try:
            strategy_type = cls.__registry__[evidence_kind]
        except KeyError as exc:
            raise ValidationReferenceError(
                f"No trusted-reference strategy is registered for {evidence_kind.value!r}."
            ) from exc
        return strategy_type()

    @abstractmethod
    def materialize(
        self,
        record: ValidationReferenceRecord,
        source: Path,
        target: Path,
    ) -> None:
        """Materialize one reference into the trusted scoring surface."""

    @abstractmethod
    def load(self, path: Path) -> np.ndarray:
        """Load one prepared reference as an instance-label array."""


class Bbbc039InstanceMaskReference(ValidationReferenceStrategy):
    """Apply the pinned BBBC039 author's first-channel component decoder."""

    evidence_kind = ValidationEvidenceKind.INSTANCE_MASKS

    def materialize(
        self,
        record: ValidationReferenceRecord,
        source: Path,
        target: Path,
    ) -> None:
        del record
        if target.suffix.lower() != ".npz":
            raise ValidationReferenceError(
                f"Decoded BBBC039 references require .npz targets, got {target}."
            )
        target.parent.mkdir(parents=True, exist_ok=True)
        np.savez_compressed(target, labels=decode_bbbc039_mask(source))

    def load(self, path: Path) -> np.ndarray:
        with np.load(path, allow_pickle=False) as archive:
            return np.asarray(archive["labels"])


class Bbbc007ManualOutlineReference(ValidationReferenceStrategy):
    """Preserve manual outline pixels and decode closed regions for object metrics."""

    evidence_kind = ValidationEvidenceKind.MANUAL_OUTLINES

    def materialize(
        self,
        record: ValidationReferenceRecord,
        source: Path,
        target: Path,
    ) -> None:
        del record
        target.parent.mkdir(parents=True, exist_ok=True)
        try:
            os.link(source, target)
        except OSError:
            shutil.copy2(source, target)

    def load(self, path: Path) -> np.ndarray:
        return decode_bbbc007_outline(path)


def decode_bbbc039_mask(path: Path) -> np.ndarray:
    """Decode a BBBC039 colour mask using the pinned author's stated procedure."""

    image = np.asarray(iio.imread(path))
    if image.ndim < 2:
        raise ValidationReferenceError(f"Invalid BBBC039 mask shape {image.shape!r}.")
    first_channel = image[..., 0] if image.ndim == 3 else image
    return label(first_channel, background=0).astype(np.uint16, copy=False)


def decode_bbbc007_outline(path: Path) -> np.ndarray:
    """Convert closed white regions separated by manual black outlines to labels."""

    image = np.asarray(iio.imread(path))
    if image.ndim != 2:
        raise ValidationReferenceError(
            f"Invalid BBBC007 outline shape {image.shape!r}."
        )
    regions = label(image != 0, connectivity=1)
    border_labels = np.unique(
        np.concatenate((regions[0], regions[-1], regions[:, 0], regions[:, -1]))
    )
    regions[np.isin(regions, border_labels[border_labels != 0])] = 0
    return relabel_sequential(regions)[0]
