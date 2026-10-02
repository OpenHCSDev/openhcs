"""Image snapshot records for runtime equivalence."""

from __future__ import annotations

from dataclasses import dataclass, field, fields
from pathlib import Path

import imageio.v3 as imageio
import numpy as np

from openhcs.core.equivalence.arrays import (
    canonical_numpy_array,
    semantic_array_payload,
)
from openhcs.core.equivalence.policy import RuntimeEquivalencePolicy
from openhcs.core.source_projection import SourceArtifactProjection
from openhcs.core.source_image_provenance import SourcePlaneIndexedMetadata
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_matching import source_component_metadata_value


@dataclass(frozen=True, slots=True)
class RuntimeImageSnapshot:
    """Semantic snapshot of one exported runtime image."""

    physical_paths: tuple[Path, ...]
    shape: tuple[int, ...]
    dtype: str
    pixel_digest: str
    pixel_data: np.ndarray = field(repr=False, compare=False)

    def __post_init__(self) -> None:
        paths = tuple(Path(path) for path in self.physical_paths)
        if not paths or len(set(paths)) != len(paths):
            raise ValueError("Image snapshot requires nonempty unique physical paths.")
        object.__setattr__(self, "physical_paths", paths)

    @property
    def path(self) -> Path:
        """Return the representative path; physical_paths owns file coverage."""
        return self.physical_paths[0]

    @classmethod
    def from_image_file(cls, path: Path) -> "RuntimeImageSnapshot":
        """Read an image export into a decoded-pixel semantic snapshot."""
        array = (
            np.load(path)
            if path.suffix.lower() == ".npy"
            else np.asarray(imageio.imread(path))
        )
        return cls.from_array(path, array)

    @classmethod
    def from_array(
        cls,
        path: Path | str,
        array: object,
    ) -> "RuntimeImageSnapshot":
        """Build a semantic image snapshot from an in-memory runtime artifact."""
        contiguous = canonical_numpy_array(array)
        if contiguous is None:
            contiguous = np.ascontiguousarray(array)
        array_payload = semantic_array_payload(contiguous)
        if array_payload is None:
            raise TypeError(f"Cannot build image snapshot from {type(array)!r}.")
        return cls(
            physical_paths=(Path(path),),
            shape=tuple(int(axis) for axis in contiguous.shape),
            dtype=str(contiguous.dtype),
            pixel_digest=array_payload[3],
            pixel_data=contiguous.copy(),
        )

    @classmethod
    def from_source_planes(
        cls,
        projections: tuple[SourceArtifactProjection, ...],
        *,
        workspace_root: Path,
    ) -> "RuntimeImageSnapshot":
        """Decode one validated typed Z cohort without dropping file ownership."""
        arrays = []
        paths = []
        metadata_values = []
        for plane_index, projection in enumerate(projections):
            metadata = projection.persisted_image_metadata()
            if metadata is None or metadata.plane_axis is not None:
                raise ValueError(
                    "Exported source planes require scalar image metadata."
                )
            if metadata.source_channel_axis is not None:
                raise ValueError(
                    "Exported Z planes cannot carry an undeclared color axis."
                )
            indexed_metadata = SourcePlaneIndexedMetadata.from_metadata(
                metadata.source_component_metadata or {},
                expected_plane_count=len(projections),
            )
            if (
                indexed_metadata is not None
                and indexed_metadata.scalar_plane_index != plane_index
            ):
                raise ValueError(
                    "Exported Z planes conflict with their declared plane order."
                )
            for component, expected in projection.source_component_values():
                value = source_component_metadata_value(
                    metadata.source_component_metadata, component
                )
                if value is not None and str(value) != expected:
                    raise ValueError(
                        "Exported image metadata conflicts with its source address."
                    )
            path = (workspace_root / projection.ref.backend_address).absolute()
            if projection.ref.backend != "disk":
                raise ValueError(
                    "Physical image comparison requires disk source references."
                )
            snapshot = cls.from_image_file(path)
            array = np.asarray(projection.ref.project_source_axes(snapshot.pixel_data))
            if array.ndim != 2:
                raise ValueError(
                    "Exported Z planes require exactly two spatial pixel axes."
                )
            metadata.source_spatial_domain.require_image_window(array.shape)
            if (
                metadata.source_dtype is not None
                and np.dtype(metadata.source_dtype) != array.dtype
            ):
                raise ValueError(
                    "Exported image pixels conflict with their declared dtype."
                )
            arrays.append(array)
            paths.append(path)
            metadata_values.append(
                tuple(
                    (declaration.name, getattr(metadata, declaration.name))
                    for declaration in fields(ImagePayloadMetadata)
                    if declaration.name != "source_provenance"
                )
            )
        if not arrays:
            raise ValueError("Cannot compare an empty exported image cohort.")
        if any(value != metadata_values[0] for value in metadata_values[1:]):
            raise ValueError("Exported Z planes have incompatible image metadata.")
        if any(
            array.shape != arrays[0].shape or array.dtype != arrays[0].dtype
            for array in arrays[1:]
        ):
            raise ValueError(
                "Exported Z planes must share an exact pixel shape and dtype."
            )
        volume = cls.from_array(paths[0], np.stack(arrays))
        return cls(
            physical_paths=tuple(dict.fromkeys(paths)),
            shape=volume.shape,
            dtype=volume.dtype,
            pixel_digest=volume.pixel_digest,
            pixel_data=volume.pixel_data,
        )

    def content_key(
        self,
        policy: RuntimeEquivalencePolicy,
    ) -> tuple[object, ...]:
        """Return image identity at the requested semantic strictness."""
        key: tuple[object, ...] = (self.shape, self.dtype)
        if policy.compare_image_pixels:
            key = (*key, self.pixel_digest)
        return key
