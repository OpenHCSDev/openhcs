"""Sparse IJV object-label storage and identity-domain semantics."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from types import MappingProxyType
from typing import Any, ClassVar, cast

import numpy as np
from openhcs.core.runtime_object_label_domains import ObjectLabelIdDomainStrategy
from openhcs.core.runtime_tabular_values import FieldSpec
from openhcs.core.runtime_tabular_values import ColumnarRows
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisValueProjection,
)
from openhcs.core.source_spatial_domain import SourceSpatialDomain, SpatialShapeYX

SINGLETON_AXIS_LENGTH = 1


@dataclass(frozen=True, slots=True)
class SparseIJVLabelRows(ColumnarRows):
    """Sparse object-label table: one row per labelled pixel of a plane.

    Columns are the planar spatial domain's axes followed by the label, which
    is CellProfiler's IJV layout.
    """

    data: Any
    slice_count: int | None = None

    YX_LABEL_FIELDS: ClassVar[tuple[FieldSpec, ...]] = (
        *(FieldSpec(name, int) for name in SourceSpatialDomain.axis_names),
        FieldSpec("label", int),
    )
    SLICE_INDEX_FIELD: ClassVar[FieldSpec] = FieldSpec("slice_index", int)

    def __post_init__(self) -> None:
        array = self.as_array()
        if array.ndim != 2 or array.shape[1] not in (3, 4):
            raise ValueError(
                "SparseIJVLabelRows.data must be an N x 3 y/x/label table "
                "or an N x 4 slice/y/x/label table."
            )
        self.validate_fields()
        if self.slice_count is None:
            return
        normalized_count = int(self.slice_count)
        if normalized_count < 0:
            raise ValueError("SparseIJVLabelRows.slice_count cannot be negative.")
        if not self.has_slice_index:
            if normalized_count != SINGLETON_AXIS_LENGTH:
                raise ValueError(
                    "SparseIJVLabelRows without a slice_index column must have "
                    "slice_count=1."
                )
            object.__setattr__(self, "slice_count", normalized_count)
            return
        observed_count = (
            int(np.max(array[:, self.slice_column])) + SINGLETON_AXIS_LENGTH
            if array.size
            else 0
        )
        if normalized_count < observed_count:
            raise ValueError(
                "SparseIJVLabelRows.slice_count cannot be smaller than the "
                f"encoded slice indexes: {normalized_count} < {observed_count}."
            )
        object.__setattr__(self, "slice_count", normalized_count)

    @property
    def columns(self) -> Mapping[str, Any]:
        array = self.as_array()
        return MappingProxyType(
            {
                field_spec.name: array[:, column_index]
                for column_index, field_spec in enumerate(self.fields)
            }
        )

    @property
    def fields(self) -> tuple[FieldSpec, ...]:
        """Return the exact integer schema for this sparse layout."""
        if self.has_slice_index:
            return (self.SLICE_INDEX_FIELD, *self.YX_LABEL_FIELDS)
        return self.YX_LABEL_FIELDS

    def runtime_slice_count(self) -> int | None:
        return self.slice_count

    def value_for_slice(
        self, context: RuntimePlaneAxisValueProjection
    ) -> "SparseIJVLabelRows":
        if context.axis is not RuntimePlaneAxis.RUNTIME_SLICE:
            return self
        return self.slice(context.require_plane_index())

    @property
    def has_slice_index(self) -> bool:
        return int(self.as_array().shape[1]) == 4

    @property
    def slice_column(self) -> int:
        if not self.has_slice_index:
            raise ValueError("SparseIJVLabelRows has no slice_index column.")
        return 0

    @property
    def y_column(self) -> int:
        return 1 if self.has_slice_index else 0

    @property
    def x_column(self) -> int:
        return 2 if self.has_slice_index else 1

    @property
    def label_column(self) -> int:
        return 3 if self.has_slice_index else 2

    @classmethod
    def from_label_slice(cls, labels: object) -> "SparseIJVLabelRows":
        """Return sparse-IJV rows for one object-label slice payload."""
        if isinstance(labels, cls):
            return labels
        return cls(labels)

    @classmethod
    def from_dense_labels(cls, labels: Any) -> "SparseIJVLabelRows":
        label_array = np.asarray(labels)
        if label_array.ndim != 2:
            raise ValueError(
                "SparseIJVLabelRows.from_dense_labels requires a 2-D label image."
            )
        rows, columns = np.nonzero(label_array > 0)
        if rows.size == 0:
            return cls(np.zeros((0, 3), dtype=np.int32))
        return cls(
            np.column_stack((rows, columns, label_array[rows, columns])).astype(
                np.int32,
                copy=False,
            )
        )

    @classmethod
    def from_dense_stack(cls, labels: Any) -> "SparseIJVLabelRows":
        """Build sparse rows from a 2-D label image or runtime-slice stack."""
        label_array = np.asarray(labels)
        if label_array.ndim == 2:
            return cls.from_dense_labels(label_array)
        if label_array.ndim != 3:
            raise ValueError(
                "SparseIJVLabelRows.from_dense_stack requires a 2-D label image "
                "or a 3-D runtime-slice label stack; got "
                f"shape {tuple(label_array.shape)!r}."
            )
        slices = tuple(
            cls.from_dense_labels(slice_labels) for slice_labels in label_array
        )
        return cls.from_slices(slices)

    @classmethod
    def from_slices(
        cls, values: Sequence["SparseIJVLabelRows"]
    ) -> "SparseIJVLabelRows":
        arrays = []
        for slice_index, value in enumerate(values):
            array = value.as_yx_label_array()
            if not array.size:
                continue
            arrays.append(
                np.column_stack(
                    (
                        np.full(array.shape[0], slice_index, dtype=np.int32),
                        array,
                    )
                )
            )
        return cls(
            (
                np.vstack(arrays).astype(np.int32, copy=False)
                if arrays
                else np.zeros((0, 4), dtype=np.int32)
            ),
            slice_count=len(values),
        )

    def as_yx_label_array(self) -> Any:
        array = self.as_array()
        if not self.has_slice_index:
            return array
        return array[:, (self.y_column, self.x_column, self.label_column)]

    def slice_indices(self) -> tuple[int, ...]:
        if not self.has_slice_index:
            return (0,)
        return tuple(
            int(index) for index in np.unique(self.as_array()[:, self.slice_column])
        )

    def slice(self, slice_index: int) -> "SparseIJVLabelRows":
        if not self.has_slice_index:
            if slice_index != 0:
                return type(self)(np.zeros((0, 3), dtype=np.int32))
            return self
        array = self.as_array()
        rows = array[array[:, self.slice_column] == int(slice_index)]
        return type(self)(rows[:, (self.y_column, self.x_column, self.label_column)])

    def to_dense(
        self,
        *,
        source_spatial_shape_yx: tuple[int, int] | None = None,
        dtype: object | None = None,
    ) -> np.ndarray:
        """Materialize sparse IJV rows as dense 2-D or slice-stacked labels."""
        array = self.as_array()
        if dtype is None:
            dtype = array.dtype if array.size else np.int32
        height, width = self._dense_spatial_shape(source_spatial_shape_yx)
        if not self.has_slice_index:
            dense = np.zeros((height, width), dtype=dtype)
            if array.size:
                dense[
                    array[:, self.y_column].astype(np.intp, copy=False),
                    array[:, self.x_column].astype(np.intp, copy=False),
                ] = array[:, self.label_column].astype(dtype, copy=False)
            return dense
        slice_count = self.label_data_runtime_slice_count()
        dense = np.zeros((slice_count, height, width), dtype=dtype)
        if array.size:
            dense[
                array[:, self.slice_column].astype(np.intp, copy=False),
                array[:, self.y_column].astype(np.intp, copy=False),
                array[:, self.x_column].astype(np.intp, copy=False),
            ] = array[:, self.label_column].astype(dtype, copy=False)
        return dense

    def nonoverlapping_dense_layers(
        self, *, source_spatial_shape_yx: tuple[int, int] | None = None,
    ) -> tuple[np.ndarray, ...]:
        """Render each object intact in a nonoverlapping label layer.

        Color the pixel-overlap graph in ascending degree/label order, matching
        CellProfiler's sparse segmentation layer ordering. Touching objects may
        share a layer; only shared pixels create graph edges.
        """
        if self.has_slice_index:
            raise ValueError("Label rendering requires a projected sparse label plane.")
        rows = self.as_array()
        height, width = self._dense_spatial_shape(source_spatial_shape_yx)
        if not rows.size:
            return (np.zeros((height, width), dtype=np.int32),)
        rows = rows[rows[:, self.label_column] > 0]
        if not rows.size:
            return (np.zeros((height, width), dtype=np.int32),)
        label_ids, label_ordinals = np.unique(
            rows[:, self.label_column], return_inverse=True,
        )
        ordered = np.unique(rows, axis=0)
        edges = []
        # Compare rows within each coordinate run. This bounds work by actual
        # pixel multiplicity rather than comparing every pair of objects.
        breaks = np.r_[
            0,
            np.flatnonzero(np.any(ordered[1:, :2] != ordered[:-1, :2], axis=1)) + 1,
            len(ordered),
        ]
        for offset in range(1, int(np.max(np.diff(breaks)))):
            same_pixel = np.all(ordered[:-offset, :2] == ordered[offset:, :2], axis=1)
            pairs = np.column_stack((
                ordered[:-offset, 2][same_pixel], ordered[offset:, 2][same_pixel],
            ))
            edges.extend((pairs, pairs[:, ::-1]))
        colors = np.ones(len(label_ids), dtype=np.intp)
        if edges:
            pairs = np.searchsorted(label_ids, np.unique(np.concatenate(edges), axis=0))
            degree = np.bincount(pairs[:, 0].astype(np.intp), minlength=len(colors))
            starts = np.cumsum(degree) - degree
            overlapping = np.flatnonzero(degree)
            colors[overlapping] = 0
            for label in overlapping[np.lexsort((overlapping, degree[overlapping]))]:
                neighbors = pairs[starts[label]:starts[label] + degree[label], 1]
                used = set(colors[neighbors])
                color = 1
                while color in used:
                    color += 1
                colors[label] = color
        dense = np.zeros((int(np.max(colors)), height, width), dtype=rows.dtype)
        dense[
            colors[label_ordinals] - 1, rows[:, self.y_column], rows[:, self.x_column],
        ] = rows[:, self.label_column]
        return tuple(dense)

    def label_data_runtime_slice_count(self) -> int:
        """Return the encoded runtime-slice count, including empty stacks."""
        if not self.has_slice_index:
            return SINGLETON_AXIS_LENGTH
        if self.slice_count is not None:
            return self.slice_count
        slice_indices = self.slice_indices()
        if not slice_indices:
            return 0
        return max(slice_indices) + SINGLETON_AXIS_LENGTH

    def _dense_spatial_shape(
        self,
        source_spatial_shape_yx: tuple[int, int] | None,
    ) -> tuple[int, int]:
        if source_spatial_shape_yx is not None:
            return SpatialShapeYX.from_sequence(
                source_spatial_shape_yx,
                field_name="source_spatial_shape_yx",
            ).as_tuple()
        array = self.as_array()
        if not array.size:
            return (0, 0)
        return (
            int(np.max(array[:, self.y_column])) + 1,
            int(np.max(array[:, self.x_column])) + 1,
        )

    def as_array(self) -> np.ndarray:
        return np.asarray(self.data)


class SparseIJVLabelRowsIdDomainStrategy(ObjectLabelIdDomainStrategy):
    """Extract present object IDs from sparse IJV label rows without densifying."""

    value_type = SparseIJVLabelRows

    def present_ids(self, labels: Any) -> tuple[int, ...]:
        sparse_labels = cast(SparseIJVLabelRows, labels)
        array = sparse_labels.as_array()
        if array.size == 0:
            return ()
        label_column = array[:, sparse_labels.label_column]
        return self.positive_ids_from_array(label_column)
