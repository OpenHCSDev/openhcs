"""Abstract plane provenance and metadata for tensor stack composition.

Declares the provenance and metadata interfaces that the runtime plane
axis hierarchy requires for composing, selecting and validating tensor
planes.  The microscopy layer (``SourceImageProvenance``,
``ImagePayloadMetadata``) implements these protocols; arraypipe consumers
use only these interfaces.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Sequence
from typing import Self


class PlaneMetadata(ABC):
    """Metadata a tensor value carries about its plane structure.

    Subclasses carry domain-specific information (source provenance,
    spatial calibration, intensity scaling).  The tensor infrastructure
    reads only the abstract properties declared here.
    """

    __slots__ = ()

    @property
    @abstractmethod
    def source_provenance(self) -> PlaneProvenance:
        """The provenance of this value's data planes."""

    @abstractmethod
    def axis_position(self, role: type) -> int | None:
        """Return the rank-relative position of the axis carrying ``role``."""


class PlaneProvenance(ABC):
    """Provenance of a tensor plane stack: where each plane came from.

    Subclasses carry domain-specific identity (source images, file paths,
    acquisition metadata).  The tensor infrastructure reads only these
    abstract properties and composition methods.
    """

    __slots__ = ()

    @property
    @abstractmethod
    def source_plane_count(self) -> int:
        """How many planes this provenance covers."""

    @property
    @abstractmethod
    def source_image_names(self) -> tuple[str, ...]:
        """Alias names identifying each plane's data source."""

    @abstractmethod
    def for_source_plane(self, plane_index: int) -> Self:
        """Return the provenance of one selected plane."""

    @classmethod
    @abstractmethod
    def stack(
        cls,
        provenances: Sequence[PlaneProvenance],
        *,
        scalar_sources: Sequence[PlaneProvenance],
        **topology: bool,
    ) -> PlaneProvenance:
        """Compose provenances by stacking planes along the leading axis."""

    @classmethod
    @abstractmethod
    def bundle(
        cls,
        provenances: Sequence[PlaneProvenance],
        *,
        scalar_sources: Sequence[PlaneProvenance],
        **topology: bool,
    ) -> PlaneProvenance:
        """Compose provenances by bundling data-source planes."""
