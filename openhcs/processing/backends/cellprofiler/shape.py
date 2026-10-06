"""Shape-measurement backends for CellProfiler-compatible processing."""

from __future__ import annotations
from typing import Annotated, ClassVar, TYPE_CHECKING, TypeAlias
from openhcs.interop.cellprofiler.settings_binder import (
    SettingToKeywordBinding,
    parse_cellprofiler_bool,
)
from openhcs.core.runtime_tabular_values import (
    FieldSpec,
    MeasurementObjectRowIdentity,
)
from openhcs.core.runtime_measurements import (
    ObjectFeatureMissingValue,
    RuntimeMeasurementFeature,
    RuntimeMeasurementFeatureSemanticMarker,
)
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.interop.cellprofiler.module_measurement_features import (
    MeasuredObjectAnchorFeature,
    ObjectLocationFeature,
    ShapeDescriptorFeature,
)
from openhcs.interop.cellprofiler.module_artifact_declarations import (
    ObjectMeasurementInputModule,
    PerObjectMeasurementExecutionModule,
)
from openhcs.interop.cellprofiler.runtime.object_measurement_row_policies import (
    DeclaredDomainCompactMeasuredObjectMeasurementRowPolicy,
    DenseColumnarObjectMeasurementRowsMixin,
)
from openhcs.interop.cellprofiler.runtime.measurement_recording import (
    CurrentPayloadMeasurementRecordMixin,
)
from openhcs.interop.cellprofiler.runtime.object_input_policies import (
    LabelsObjectInputPolicy,
)
from openhcs.processing.backends.cellprofiler._backend import (
    CellProfilerBackendProvider,
)
from openhcs.processing.backends.cellprofiler.perf_fixtures import (
    capture_array_fixture,
)
from openhcs.processing.backends.analysis.region_properties import (
    AnalysisBackendProvider,
)
from openhcs.processing.backends.cellprofiler.zernike import (
    ShapeZernikeFeatureAuthority,
    ShapeObjectZernikeDescriptorDeclaration,
)
from openhcs.core.runtime_object_labels import ObjectLabelVariantData

if TYPE_CHECKING:
    from openhcs.interop.cellprofiler.module_settings import BoundModuleSettings
    from openhcs.interop.cellprofiler.parser import ModuleBlock
    from openhcs.interop.cellprofiler.runtime.invocation import (
        CellProfilerMeasurementImage,
    )


class ZeroFilledShapeFeature(RuntimeMeasurementFeatureSemanticMarker):
    """Native shape vector padded with zero through the material object extent."""


class LabelIndexedShapeFeature(RuntimeMeasurementFeatureSemanticMarker):
    """Shape vector whose values retain their measured label identities."""


class MeasureObjectSizeShapeModule(
    LabelsObjectInputPolicy,
    CurrentPayloadMeasurementRecordMixin,
    DenseColumnarObjectMeasurementRowsMixin,
    DeclaredDomainCompactMeasuredObjectMeasurementRowPolicy,
    PerObjectMeasurementExecutionModule,
    ObjectMeasurementInputModule,
    MeasuredObjectAnchorFeature,
    ShapeZernikeFeatureAuthority,
):
    module_name = "MeasureObjectSizeShape"
    function_name = "measure_object_size_shape"
    validated = True
    confidence = 1.0
    ignored_settings = ("Select objects to measure", "Select object sets to measure")
    measurement_category_prefixes = (("area", "shape"), ("location",))

    class MeasurementFeature(RuntimeMeasurementFeature):
        """Feature families emitted by MeasureObjectSizeShape."""

        AREA = (
            "Area",
            (),
            (MeasuredObjectAnchorFeature, ShapeDescriptorFeature),
        )
        PERIMETER = ("Perimeter", (), (ShapeDescriptorFeature,))
        VOLUME = ("Volume", (), (ShapeDescriptorFeature,))
        SURFACE_AREA = ("SurfaceArea", (), (ShapeDescriptorFeature,))
        ECCENTRICITY = ("Eccentricity", (), (ShapeDescriptorFeature,))
        SOLIDITY = ("Solidity", (), (ShapeDescriptorFeature,))
        CONVEX_AREA = ("ConvexArea", (), (ShapeDescriptorFeature,))
        EXTENT = ("Extent", (), (ShapeDescriptorFeature,))
        CENTER_X = (
            "Center_X",
            (),
            (
                MeasuredObjectAnchorFeature,
                ShapeDescriptorFeature,
                ObjectLocationFeature,
            ),
        )
        CENTER_Y = (
            "Center_Y",
            (),
            (
                MeasuredObjectAnchorFeature,
                ShapeDescriptorFeature,
                ObjectLocationFeature,
            ),
        )
        CENTER_Z = ("Center_Z", (), (ShapeDescriptorFeature, ObjectLocationFeature))
        BOUNDING_BOX_AREA = ("BoundingBoxArea", (), (ShapeDescriptorFeature,))
        BOUNDING_BOX_VOLUME = ("BoundingBoxVolume", (), (ShapeDescriptorFeature,))
        BOUNDING_BOX_MINIMUM_X = (
            "BoundingBoxMinimum_X",
            (),
            (ShapeDescriptorFeature,),
        )
        BOUNDING_BOX_MAXIMUM_X = (
            "BoundingBoxMaximum_X",
            (),
            (ShapeDescriptorFeature,),
        )
        BOUNDING_BOX_MINIMUM_Y = (
            "BoundingBoxMinimum_Y",
            (),
            (ShapeDescriptorFeature,),
        )
        BOUNDING_BOX_MAXIMUM_Y = (
            "BoundingBoxMaximum_Y",
            (),
            (ShapeDescriptorFeature,),
        )
        BOUNDING_BOX_MINIMUM_Z = (
            "BoundingBoxMinimum_Z",
            (),
            (ShapeDescriptorFeature,),
        )
        BOUNDING_BOX_MAXIMUM_Z = (
            "BoundingBoxMaximum_Z",
            (),
            (ShapeDescriptorFeature,),
        )
        EULER_NUMBER = ("EulerNumber", (), (ShapeDescriptorFeature,))
        FORM_FACTOR = ("FormFactor", (), (ShapeDescriptorFeature,))
        MAJOR_AXIS_LENGTH = ("MajorAxisLength", (), (ShapeDescriptorFeature,))
        MINOR_AXIS_LENGTH = ("MinorAxisLength", (), (ShapeDescriptorFeature,))
        ORIENTATION = ("Orientation", (), (ShapeDescriptorFeature,))
        COMPACTNESS = ("Compactness", (), (ShapeDescriptorFeature,))
        MAXIMUM_RADIUS = (
            "MaximumRadius",
            (),
            (ShapeDescriptorFeature, ZeroFilledShapeFeature),
        )
        MEDIAN_RADIUS = (
            "MedianRadius",
            (),
            (ShapeDescriptorFeature, ZeroFilledShapeFeature),
        )
        MEAN_RADIUS = (
            "MeanRadius",
            (),
            (ShapeDescriptorFeature, ZeroFilledShapeFeature),
        )
        MIN_FERET_DIAMETER = (
            "MinFeretDiameter",
            (),
            (ShapeDescriptorFeature, LabelIndexedShapeFeature, ZeroFilledShapeFeature),
        )
        MAX_FERET_DIAMETER = (
            "MaxFeretDiameter",
            (),
            (ShapeDescriptorFeature, LabelIndexedShapeFeature, ZeroFilledShapeFeature),
        )
        EQUIVALENT_DIAMETER = ("EquivalentDiameter", (), (ShapeDescriptorFeature,))
        SPATIAL_MOMENT = ("SpatialMoment", (), (ShapeDescriptorFeature,))
        CENTRAL_MOMENT = ("CentralMoment", (), (ShapeDescriptorFeature,))
        NORMALIZED_MOMENT = ("NormalizedMoment", (), (ShapeDescriptorFeature,))
        HU_MOMENT = ("HuMoment", (), (ShapeDescriptorFeature,))
        INERTIA_TENSOR = ("InertiaTensor", (), (ShapeDescriptorFeature,))
        INERTIA_TENSOR_EIGENVALUES = (
            "InertiaTensorEigenvalues",
            (),
            (ShapeDescriptorFeature,),
        )

        def indexed_name(self, *indices: int) -> str:
            if not indices:
                return self.value
            return "_".join((self.value, *(str(int(index)) for index in indices)))

    zernike_max_order = 9
    standard_2d_features = (
        MeasurementFeature.AREA,
        MeasurementFeature.PERIMETER,
        MeasurementFeature.MAJOR_AXIS_LENGTH,
        MeasurementFeature.MINOR_AXIS_LENGTH,
        MeasurementFeature.ECCENTRICITY,
        MeasurementFeature.ORIENTATION,
        MeasurementFeature.CENTER_X,
        MeasurementFeature.CENTER_Y,
        MeasurementFeature.BOUNDING_BOX_AREA,
        MeasurementFeature.BOUNDING_BOX_MINIMUM_X,
        MeasurementFeature.BOUNDING_BOX_MAXIMUM_X,
        MeasurementFeature.BOUNDING_BOX_MINIMUM_Y,
        MeasurementFeature.BOUNDING_BOX_MAXIMUM_Y,
        MeasurementFeature.FORM_FACTOR,
        MeasurementFeature.EXTENT,
        MeasurementFeature.SOLIDITY,
        MeasurementFeature.COMPACTNESS,
        MeasurementFeature.EULER_NUMBER,
        MeasurementFeature.MAXIMUM_RADIUS,
        MeasurementFeature.MEAN_RADIUS,
        MeasurementFeature.MEDIAN_RADIUS,
        MeasurementFeature.CONVEX_AREA,
        MeasurementFeature.MIN_FERET_DIAMETER,
        MeasurementFeature.MAX_FERET_DIAMETER,
        MeasurementFeature.EQUIVALENT_DIAMETER,
    )
    standard_3d_features = (
        MeasurementFeature.VOLUME,
        MeasurementFeature.SURFACE_AREA,
        MeasurementFeature.MAJOR_AXIS_LENGTH,
        MeasurementFeature.MINOR_AXIS_LENGTH,
        MeasurementFeature.CENTER_X,
        MeasurementFeature.CENTER_Y,
        MeasurementFeature.CENTER_Z,
        MeasurementFeature.BOUNDING_BOX_VOLUME,
        MeasurementFeature.BOUNDING_BOX_MINIMUM_X,
        MeasurementFeature.BOUNDING_BOX_MAXIMUM_X,
        MeasurementFeature.BOUNDING_BOX_MINIMUM_Y,
        MeasurementFeature.BOUNDING_BOX_MAXIMUM_Y,
        MeasurementFeature.BOUNDING_BOX_MINIMUM_Z,
        MeasurementFeature.BOUNDING_BOX_MAXIMUM_Z,
        MeasurementFeature.EXTENT,
        MeasurementFeature.EULER_NUMBER,
        MeasurementFeature.EQUIVALENT_DIAMETER,
    )
    advanced_2d_feature_specs = (
        (MeasurementFeature.SPATIAL_MOMENT, range(3), range(4)),
        (MeasurementFeature.CENTRAL_MOMENT, range(3), range(4)),
        (MeasurementFeature.NORMALIZED_MOMENT, range(4), range(4)),
        (MeasurementFeature.HU_MOMENT, range(7), None),
        (MeasurementFeature.INERTIA_TENSOR, range(2), range(2)),
        (MeasurementFeature.INERTIA_TENSOR_EIGENVALUES, range(2), None),
    )
    measurement_feature_part_aliases = {
        tuple(MeasurementFeature.AREA.feature_family().split("_")): (
            tuple(MeasurementFeature.VOLUME.feature_family().split("_")),
        ),
        tuple(MeasurementFeature.BOUNDING_BOX_AREA.feature_family().split("_")): (
            tuple(MeasurementFeature.BOUNDING_BOX_VOLUME.feature_family().split("_")),
        ),
        tuple(MeasurementFeature.PERIMETER.feature_family().split("_")): (
            tuple(MeasurementFeature.SURFACE_AREA.feature_family().split("_")),
        ),
    }

    def table_source_image_name(
        self,
        measurement_images: tuple["CellProfilerMeasurementImage", ...],
        source_image_name: str | None,
    ) -> str | None:
        """AreaShape rows are object-owned, not image-source-owned."""
        del measurement_images, source_image_name
        return None

    @classmethod
    def project_measurement_record_rows(
        cls,
        rows: "ColumnarRows",
        *,
        source_image_name: str | None,
    ) -> "ColumnarRows":
        """Project declared shape fields to their CellProfiler category."""
        del source_image_name
        declared_fields = frozenset(cls.measurement_all_field_names())
        undeclared_fields = tuple(
            field_spec.name
            for field_spec in rows.fields
            if field_spec.name not in declared_fields
            and field_spec.name not in MeasurementRowAxisField.field_names()
        )
        if undeclared_fields:
            raise ValueError(
                f"{cls.__name__} emitted undeclared shape fields {undeclared_fields!r}."
            )
        category = "".join(
            part[:1].upper() + part[1:] for part in cls.measurement_category_prefixes[0]
        )
        feature_fields = declared_fields - MeasurementRowAxisField.field_names()
        projected_field_columns = tuple(
            (
                (
                    FieldSpec(
                        name=f"{category}_{field_spec.name}",
                        dtype=field_spec.dtype,
                        required=field_spec.required,
                    )
                    if field_spec.name in feature_fields
                    else field_spec
                ),
                rows.column_values(field_spec.name),
            )
            for field_spec in rows.fields
        )
        projected_columns = MappingProxyType(
            {field_spec.name: values for field_spec, values in projected_field_columns}
        )
        if len(projected_columns) != len(rows.fields):
            raise ValueError(
                f"{cls.__name__} shape feature projection produced duplicate "
                "field identities."
            )
        return MeasurementProjectedColumnarRows(
            projected_columns,
            fields=tuple(field_spec for field_spec, _values in projected_field_columns),
            declared_object_measurement_domain_covered=(
                rows.covers_declared_object_measurement_domain
            ),
            object_row_identity=rows.object_row_identity,
        )

    @classmethod
    def indexed_feature_names(
        cls,
        specs: tuple[tuple[MeasurementFeature, range, range | None], ...],
    ) -> tuple[str, ...]:
        fields: list[str] = []
        for feature, rows, columns in specs:
            if columns is None:
                fields.extend(feature.indexed_name(row) for row in rows)
            else:
                fields.extend(
                    feature.indexed_name(row, column)
                    for row in rows
                    for column in columns
                )
        return tuple(fields)

    @classmethod
    def measurement_field_names(
        cls,
        *,
        dimensions: int = 2,
        calculate_advanced: bool = True,
        calculate_zernikes: bool = True,
        object_id_field: str = "object_label",
        slice_index_field: str = "slice_index",
    ) -> tuple[str, ...]:
        if dimensions not in (2, 3):
            raise ValueError(
                f"Object shape measurements support 2D/3D, got {dimensions}D."
            )
        fields: list[str] = [slice_index_field, object_id_field]
        if dimensions == 2:
            fields.extend(feature.value for feature in cls.standard_2d_features)
            if calculate_advanced:
                fields.extend(cls.indexed_feature_names(cls.advanced_2d_feature_specs))
            if calculate_zernikes:
                fields.extend(
                    cls.shape_zernike_feature_names(max_order=cls.zernike_max_order)
                )
        else:
            fields.extend(feature.value for feature in cls.standard_3d_features)
            if calculate_advanced:
                fields.append(cls.MeasurementFeature.SOLIDITY.value)
        return tuple(dict.fromkeys(fields))

    @classmethod
    def measurement_all_field_names(
        cls,
        *,
        calculate_advanced: bool = True,
        calculate_zernikes: bool = True,
        object_id_field: str = "object_label",
        slice_index_field: str = "slice_index",
    ) -> tuple[str, ...]:
        return tuple(
            dict.fromkeys(
                (
                    *cls.measurement_field_names(
                        dimensions=2,
                        calculate_advanced=calculate_advanced,
                        calculate_zernikes=calculate_zernikes,
                        object_id_field=object_id_field,
                        slice_index_field=slice_index_field,
                    ),
                    *cls.measurement_field_names(
                        dimensions=3,
                        calculate_advanced=calculate_advanced,
                        calculate_zernikes=calculate_zernikes,
                        object_id_field=object_id_field,
                        slice_index_field=slice_index_field,
                    ),
                )
            )
        )

    zernike_backend_provider = CellProfilerBackendProvider.LEGACY_FAST
    regionprops_backend_provider = AnalysisBackendProvider.NUMBA
    setting_bindings = (
        SettingToKeywordBinding(
            "Calculate the Zernike features?",
            "calculate_zernikes",
            parse_cellprofiler_bool,
        ),
        SettingToKeywordBinding(
            "Calculate the advanced features?",
            "calculate_advanced",
            parse_cellprofiler_bool,
        ),
    )

    @classmethod
    def postprocess_bound_settings(
        cls, module: "ModuleBlock", bound: "BoundModuleSettings"
    ) -> "BoundModuleSettings":
        """Retain the native upgrade default for pre-toggle shape modules."""
        bound = super().postprocess_bound_settings(module, bound)
        revision = module.variable_revision_number
        if (
            revision is not None
            and revision <= 2
            and "calculate_advanced" not in bound.kwargs
        ):
            return bound.with_kwargs({"calculate_advanced": False})
        return bound


from abc import ABC, abstractmethod
from collections.abc import Mapping
from dataclasses import dataclass, field
import logging
import time
from types import MappingProxyType
import numpy as np
from openhcs.processing.backends.cellprofiler._preparation import (
    CellProfilerCallableKernelPreparation,
)
from metaclass_registry import AutoRegisterMeta
from numba import njit
from openhcs.constants.constants import MemoryType
from openhcs.core.memory import numpy as numpy_decorator
from openhcs.core.pipeline.function_contracts import (
    ObjectLabelInputExecutionMode,
    object_label_input_execution_mode,
    special_inputs,
)
from openhcs.core.runtime_object_label_domains import (
    ObjectLabelDomain,
    dense_object_label_measurement_row_domain,
)
from openhcs.core.runtime_measurements import (
    MeasurementRowAxisField,
    ObjectFeatureArrayDomain,
    ObjectFeatureValueTable,
)
from openhcs.core.runtime_object_labels import (
    ObjectLabelRepresentation,
)
from openhcs.core.measurement_row_materialization import (
    MeasurementProjectedColumnarRows,
    ObjectMeasurementColumnarRows,
)
from openhcs.core.runtime_tabular_values import ColumnarRows
from openhcs.core.runtime_object_labels import (
    ObjectLabelPayload,
    ObjectLabelValue,
    object_label_dense_array,
    object_label_sparse_ijv_rows,
)
from openhcs.core.runtime_sparse_labels import SparseIJVLabelRows
from openhcs.processing.backends.analysis.region_properties import (
    LabelRegionPropertiesBackendStrategy,
)
from openhcs.processing.backends.cellprofiler._backend import (
    BackendProviderInput,
    DEFAULT_CELLPROFILER_BACKEND_SELECTION,
    CellProfilerBackendStrategyMixin,
    CellProfilerBackendAuthority,
)
from openhcs.processing.backends.cellprofiler.label_geometry import (
    feret_diameters_from_labels,
    _numpy124_aquicksort_indices,
    _numpy124_ordered_label_maximum_indices,
)
from openhcs.processing.backends.cellprofiler.morphology import (
    MorphologyBackendStrategy,
)
from openhcs.core.runtime_profile import RuntimeProfiler
from openhcs.processing.backends.cellprofiler.distance_propagation_numba import (
    _edt_1d_numba,
)
from openhcs.processing.backends.cellprofiler.zernike import shape_zernike_moments

logger = logging.getLogger(__name__)
runtime_profiler = RuntimeProfiler(logger)
ShapeFeatureArrays = tuple[dict[str, np.ndarray], np.ndarray]
ShapeFeatureRows = tuple[dict[str, np.ndarray], np.ndarray, tuple[int, ...]]
RegionpropsBackendProviderInput: TypeAlias = Annotated[
    AnalysisBackendProvider,
    "Region-properties implementation used to calculate object geometry.",
]


class ShapeObjectFeatureValueTable(ObjectFeatureValueTable):
    """Object shape feature rows with CellProfiler-compatible missing values."""

    table_label = "shape"

    def feature_array_domain(self, feature_name: str) -> ObjectFeatureArrayDomain:
        """Derive compact versus label-indexed vectors from feature declarations."""
        if (
            feature_name
            not in MeasureObjectSizeShapeModule.measurement_all_field_names()
        ):
            raise ValueError(
                f"{type(self).__name__} feature {feature_name!r} has no declared "
                "feature-array domain."
            )
        if (
            ShapeObjectZernikeDescriptorDeclaration.from_feature_name(feature_name)
            is not None
            or any(
                feature.value == feature_name
                and LabelIndexedShapeFeature.matches_feature(feature)
                for feature in MeasureObjectSizeShapeModule.MeasurementFeature
            )
        ):
            return ObjectFeatureArrayDomain.MEASURED_OBJECT_ID
        return ObjectFeatureArrayDomain.ROW_ORDINAL

    def feature_missing_value(
        self, feature_name: str, *, object_id: int,
    ) -> ObjectFeatureMissingValue:
        """Native radius/Feret vectors contain zeros within their material extent."""
        material_slot = (
            object_id - 1
            if self.feature_array_domain(feature_name)
            is ObjectFeatureArrayDomain.MEASURED_OBJECT_ID
            else self.object_domain.index(object_id)
        )
        if (
            material_slot < max(self.measured_object_ids, default=0)
            and any(
                feature.value == feature_name
                and ZeroFilledShapeFeature.matches_feature(feature)
                for feature in MeasureObjectSizeShapeModule.MeasurementFeature
            )
        ):
            return ObjectFeatureMissingValue.ZERO
        return super().feature_missing_value(feature_name, object_id=object_id)


class ShapeObjectMeasurementRows(ObjectMeasurementColumnarRows):
    """Dense AreaShape rows that already span their declared object domain."""

    object_row_identity = MeasurementObjectRowIdentity.LABEL_ID
    __slots__ = ("_columns", "_fields", "_rows")

    def __init__(
        self,
        columns: Mapping[str, tuple[object, ...]],
        fields: tuple[FieldSpec, ...],
        rows: tuple[Mapping[str, object], ...],
    ) -> None:
        self._columns = columns
        self._fields = fields
        self._rows = rows
        self.validate_fields()

    @classmethod
    def from_rows(
        cls,
        rows: list[dict[str, object]],
        *,
        declared_field_names: tuple[str, ...],
    ) -> "ShapeObjectMeasurementRows":
        row_tuple = tuple((MappingProxyType(dict(row)) for row in rows))
        declared_fields = frozenset(declared_field_names)
        if row_tuple and any(frozenset(row) != declared_fields for row in row_tuple):
            raise ValueError(
                "AreaShape columnar rows must contain exactly the declared fields."
            )
        declared_features = frozenset(
            MeasureObjectSizeShapeModule.measurement_all_field_names()
        )
        integer_axes = frozenset(
            (
                MeasurementRowAxisField.SLICE_INDEX.value,
                MeasurementRowAxisField.OBJECT_LABEL.value,
            )
        )
        unknown_fields = tuple(
            field_name
            for field_name in declared_field_names
            if field_name not in integer_axes and field_name not in declared_features
        )
        if unknown_fields:
            raise ValueError(
                f"AreaShape columnar rows contain undeclared fields {unknown_fields!r}."
            )
        fields = tuple(
            FieldSpec(
                field_name,
                int if field_name in integer_axes else float,
            )
            for field_name in declared_field_names
        )
        columns = {
            field_name: tuple((row[field_name] for row in row_tuple))
            for field_name in declared_field_names
        }
        return cls(MappingProxyType(columns), fields, row_tuple)

    @property
    def columns(self) -> Mapping[str, tuple[object, ...]]:
        return self._columns

    @property
    def fields(self) -> tuple[FieldSpec, ...]:
        return self._fields

    def __len__(self) -> int:
        return len(self._rows)

    def __iter__(self):
        return iter(self._rows)

    def __getitem__(self, index: int) -> Mapping[str, object]:
        return self._rows[index]

    def row_mappings(self) -> tuple[Mapping[str, object], ...]:
        return self._rows


@dataclass(frozen=True, slots=True)
class ObjectSizeShapeFeatureArrayOwner(ABC, metaclass=AutoRegisterMeta):
    """Shared AreaShape feature-array invocation policy for backend owners."""

    __registry_key__ = "owner_key"
    __skip_if_no_key__ = True
    owner_key = None
    calculate_advanced: bool
    calculate_zernikes: bool
    shape_backend_provider: BackendProviderInput
    zernike_backend_provider: BackendProviderInput
    regionprops_backend_provider: RegionpropsBackendProviderInput
    feature_source_voxel_spacing: SourceVoxelSpacing = field(
        default_factory=SourceVoxelSpacing,
        kw_only=True,
    )

    def feature_arrays_for_labels(
        self,
        labels: np.ndarray,
        *,
        object_domain: tuple[int, ...] | None = None,
    ) -> ShapeFeatureRows:
        measurement = ObjectSizeShapeFeatureMeasurement(
            labels=np.asarray(labels, dtype=np.int32),
            object_domain=object_domain,
            calculate_advanced=self.calculate_advanced,
            calculate_zernikes=self.calculate_zernikes,
            shape_backend_provider=self.shape_backend_provider,
            zernike_backend_provider=self.zernike_backend_provider,
            regionprops_backend_provider=self.regionprops_backend_provider,
            feature_source_voxel_spacing=self.feature_source_voxel_spacing,
        )
        feature_values, measured_object_ids = measurement.feature_arrays()
        return (
            feature_values,
            measured_object_ids,
            measurement.measurement_row_domain(measured_object_ids),
        )


@dataclass(frozen=True, slots=True)
class ObjectSizeShapeFeatureMeasurement(ObjectSizeShapeFeatureArrayOwner):
    """Backend-owned CellProfiler AreaShape feature-array measurement."""

    owner_key = "feature_measurement"
    labels: np.ndarray
    object_domain: tuple[int, ...] | None = None

    def object_indices(self, labels: np.ndarray) -> np.ndarray:
        """Return the declared CellProfiler object-index axis."""
        if self.object_domain is not None:
            return np.asarray(self.object_domain, dtype=np.int32)
        return np.arange(
            1,
            int(labels.max(initial=0)) + 1,
            dtype=np.int32,
        )

    def measurement_row_domain(
        self,
        measured_object_ids: np.ndarray,
    ) -> tuple[int, ...]:
        """Return the exact row domain written by CellProfiler for these vectors."""
        if self.object_domain is not None:
            return self.object_domain
        if np.asarray(self.labels).ndim == 2:
            return tuple(int(value) for value in self.object_indices(self.labels))
        return tuple(range(1, len(measured_object_ids) + 1))

    def feature_arrays(self) -> ShapeFeatureArrays:
        """Return feature arrays and measured label ids for 2-D or 3-D labels."""
        label_array = np.asarray(self.labels, dtype=np.int32)
        if label_array.ndim == 2:
            return self._feature_arrays_2d(label_array)
        if label_array.ndim == 3:
            return self._feature_arrays_3d(label_array)
        raise ValueError(f"Object labels must be 2D or 3D, got {label_array.ndim}D.")

    def _feature_arrays_2d(self, labels: np.ndarray) -> ShapeFeatureArrays:
        total_started_at = time.perf_counter()
        phase_started_at = time.perf_counter()
        shape_backend = ShapeMeasurementBackendStrategy.for_memory_type(
            backend_provider=self.shape_backend_provider
        )
        runtime_profiler.log(
            "moss_backend_resolution",
            time.perf_counter() - phase_started_at,
            function="measure_object_size_shape",
        )
        phase_started_at = time.perf_counter()
        fast_region_props = LabelRegionPropertiesBackendStrategy.for_memory_type(
            backend_provider=self.regionprops_backend_provider
        ).measure_2d(
            labels,
            include_advanced=self.calculate_advanced,
        )
        runtime_profiler.log(
            "moss_region_properties",
            time.perf_counter() - phase_started_at,
            function="measure_object_size_shape",
            objects=int(fast_region_props.label.size),
        )
        phase_started_at = time.perf_counter()
        props = fast_region_props.as_regionprops_table_subset(
            include_advanced=self.calculate_advanced
        )
        runtime_profiler.log(
            "moss_regionprops_table_subset",
            time.perf_counter() - phase_started_at,
            function="measure_object_size_shape",
            fields=len(props),
        )
        phase_started_at = time.perf_counter()
        convex_area, solidity = _convex_area_and_solidity_from_labels(
            labels, fast_region_props
        )
        runtime_profiler.log(
            "moss_convex_area_solidity",
            time.perf_counter() - phase_started_at,
            function="measure_object_size_shape",
            objects=int(fast_region_props.label.size),
        )
        props["convex_area"] = convex_area
        props["solidity"] = solidity
        measured_labels = np.asarray(props["label"])
        object_indices = self.object_indices(labels)
        nobjects = len(object_indices)
        if nobjects == 0:
            return ({}, measured_labels)
        perimeter = np.asarray(props["perimeter"], dtype=float)
        area = np.asarray(props["area"], dtype=float)
        phase_started_at = time.perf_counter()
        max_radius, mean_radius, median_radius = (
            shape_backend.radius_features_from_labels(labels, measured_labels)
        )
        runtime_profiler.log(
            "moss_radius_features",
            time.perf_counter() - phase_started_at,
            function="measure_object_size_shape",
            objects=nobjects,
        )
        with np.errstate(divide="ignore", invalid="ignore"):
            form_factor = 4.0 * np.pi * area / perimeter**2
        with np.errstate(divide="ignore", invalid="ignore"):
            compactness = 1.0 / form_factor
        phase_started_at = time.perf_counter()
        min_feret_diameter, max_feret_diameter = shape_backend.feret_diameters(
            labels, measured_labels
        )
        runtime_profiler.log(
            "moss_feret_diameters",
            time.perf_counter() - phase_started_at,
            function="measure_object_size_shape",
            objects=int(measured_labels.size),
        )
        center_x = np.asarray(props["centroid-1"], dtype=float)
        center_y = np.asarray(props["centroid-0"], dtype=float)
        features = {
            _shape_feature(MeasureObjectSizeShapeModule.MeasurementFeature.AREA): area,
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.PERIMETER
            ): perimeter,
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.MAJOR_AXIS_LENGTH
            ): props["major_axis_length"],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.MINOR_AXIS_LENGTH
            ): props["minor_axis_length"],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.ECCENTRICITY
            ): props["eccentricity"],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.ORIENTATION
            ): np.asarray(props["orientation"], dtype=float)
            * (180 / np.pi),
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.CENTER_X
            ): center_x,
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.CENTER_Y
            ): center_y,
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.BOUNDING_BOX_AREA
            ): props["bbox_area"],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.BOUNDING_BOX_MINIMUM_X
            ): props["bbox-1"],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.BOUNDING_BOX_MAXIMUM_X
            ): props["bbox-3"],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.BOUNDING_BOX_MINIMUM_Y
            ): props["bbox-0"],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.BOUNDING_BOX_MAXIMUM_Y
            ): props["bbox-2"],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.FORM_FACTOR
            ): form_factor,
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.EXTENT
            ): props["extent"],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.SOLIDITY
            ): props["solidity"],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.COMPACTNESS
            ): compactness,
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.EULER_NUMBER
            ): props["euler_number"],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.MAXIMUM_RADIUS
            ): max_radius,
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.MEAN_RADIUS
            ): mean_radius,
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.MEDIAN_RADIUS
            ): median_radius,
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.CONVEX_AREA
            ): props["convex_area"],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.MIN_FERET_DIAMETER
            ): min_feret_diameter,
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.MAX_FERET_DIAMETER
            ): max_feret_diameter,
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.EQUIVALENT_DIAMETER
            ): props["equivalent_diameter"],
        }
        if self.calculate_advanced:
            phase_started_at = time.perf_counter()
            features.update(_advanced_2d_features(props))
            runtime_profiler.log(
                "moss_advanced_features",
                time.perf_counter() - phase_started_at,
                function="measure_object_size_shape",
            )
        if self.calculate_zernikes:
            phase_started_at = time.perf_counter()
            features.update(
                _zernike_features(
                    labels,
                    measured_labels,
                    backend_provider=self.zernike_backend_provider,
                )
            )
            runtime_profiler.log(
                "moss_zernike_features",
                time.perf_counter() - phase_started_at,
                function="measure_object_size_shape",
                objects=nobjects,
            )
        runtime_profiler.log(
            "moss_features_2d_total",
            time.perf_counter() - total_started_at,
            function="measure_object_size_shape",
            objects=nobjects,
        )
        return (features, measured_labels)

    def _feature_arrays_3d(self, labels: np.ndarray) -> ShapeFeatureArrays:
        total_started_at = time.perf_counter()
        capture_array_fixture(
            "measure_object_size_shape_3d_input",
            labels=labels,
            calculate_advanced=np.asarray(self.calculate_advanced),
            calculate_zernikes=np.asarray(self.calculate_zernikes),
        )
        shape_backend = ShapeMeasurementBackendStrategy.for_memory_type(
            backend_provider=self.shape_backend_provider
        )
        features, measured_labels = shape_backend.feature_arrays_3d(
            labels,
            calculate_advanced=self.calculate_advanced,
            spacing=self.feature_source_voxel_spacing.spacing_for_ndim(labels.ndim),
        )
        runtime_profiler.log(
            "moss_features_3d_total",
            time.perf_counter() - total_started_at,
            function="measure_object_size_shape",
            objects=int(measured_labels.size),
        )
        return features, measured_labels


def measure_object_size_shape_feature_arrays(
    labels: np.ndarray,
    *,
    calculate_advanced: bool,
    calculate_zernikes: bool,
    shape_backend_provider: BackendProviderInput = DEFAULT_CELLPROFILER_BACKEND_SELECTION,
    zernike_backend_provider: BackendProviderInput = (
        MeasureObjectSizeShapeModule.zernike_backend_provider
    ),
    regionprops_backend_provider: RegionpropsBackendProviderInput = (
        MeasureObjectSizeShapeModule.regionprops_backend_provider
    ),
    source_voxel_spacing: SourceVoxelSpacing = SourceVoxelSpacing(),
) -> ShapeFeatureArrays:
    """Return CellProfiler AreaShape feature arrays for dense labels."""
    return ObjectSizeShapeFeatureMeasurement(
        labels=np.asarray(labels, dtype=np.int32),
        object_domain=None,
        calculate_advanced=calculate_advanced,
        calculate_zernikes=calculate_zernikes,
        shape_backend_provider=shape_backend_provider,
        zernike_backend_provider=zernike_backend_provider,
        regionprops_backend_provider=regionprops_backend_provider,
        feature_source_voxel_spacing=source_voxel_spacing,
    ).feature_arrays()


@dataclass(frozen=True, slots=True)
class ObjectSizeShapeMeasurementRowsRequest(
    ObjectSizeShapeFeatureArrayOwner,
):
    """Backend-owned AreaShape row request for dense and sparse label payloads."""

    owner_key = "object_size_shape_rows"
    labels: ObjectLabelValue

    def measurement_rows(self) -> ShapeObjectMeasurementRows:
        if self.labels.representation is ObjectLabelRepresentation.SPARSE_IJV:
            rows = SparseIJVObjectSizeShapeMeasurement(
                labels=self.labels,
                calculate_advanced=self.calculate_advanced,
                calculate_zernikes=self.calculate_zernikes,
                shape_backend_provider=self.shape_backend_provider,
                zernike_backend_provider=self.zernike_backend_provider,
                regionprops_backend_provider=self.regionprops_backend_provider,
                feature_source_voxel_spacing=self.feature_source_voxel_spacing,
            ).rows()
            measurement_dimensions = 2
        else:
            measurement_planes = self.labels.measurement_planes()
            rows = DenseObjectSizeShapeMeasurement(
                measurement_planes=measurement_planes,
                calculate_advanced=self.calculate_advanced,
                calculate_zernikes=self.calculate_zernikes,
                shape_backend_provider=self.shape_backend_provider,
                zernike_backend_provider=self.zernike_backend_provider,
                regionprops_backend_provider=self.regionprops_backend_provider,
                feature_source_voxel_spacing=self.feature_source_voxel_spacing,
            ).rows()
            dimensions = tuple(
                dict.fromkeys(
                    object_label_dense_array(plane).ndim for plane in measurement_planes
                )
            )
            if len(dimensions) != 1:
                raise ValueError(
                    "AreaShape measurement planes require one common dimensionality, "
                    f"got {dimensions!r}."
                )
            measurement_dimensions = dimensions[0]
        return ShapeObjectMeasurementRows.from_rows(
            rows,
            declared_field_names=MeasureObjectSizeShapeModule.measurement_field_names(
                dimensions=measurement_dimensions,
                calculate_advanced=self.calculate_advanced,
                calculate_zernikes=self.calculate_zernikes,
            ),
        )


@numpy_decorator(contract=ProcessingContract.FLEXIBLE)
@object_label_input_execution_mode(ObjectLabelInputExecutionMode.FULL_STACK)
@special_inputs(MeasureObjectSizeShapeModule.label_kwarg)
def measure_object_size_shape(
    image: np.ndarray,
    labels: ObjectLabelValue,
    calculate_advanced: bool = True,
    calculate_zernikes: bool = True,
    shape_backend_provider: BackendProviderInput = DEFAULT_CELLPROFILER_BACKEND_SELECTION,
    zernike_backend_provider: BackendProviderInput = (
        MeasureObjectSizeShapeModule.zernike_backend_provider
    ),
    regionprops_backend_provider: RegionpropsBackendProviderInput = (
        MeasureObjectSizeShapeModule.regionprops_backend_provider
    ),
    slice_index: int | None = None,
) -> tuple[np.ndarray, ShapeObjectMeasurementRows]:
    """Measure CellProfiler AreaShape rows for labeled objects.

    Args:
        labels: Object regions whose area, perimeter, geometry, and optional
            Zernike features are measured.
        slice_index: Optional zero-based source-plane index recorded on 2-D
            measurement rows.
    """
    total_started_at = time.perf_counter()
    del slice_index
    measurement_rows = ObjectSizeShapeMeasurementRowsRequest(
        labels=labels,
        calculate_advanced=calculate_advanced,
        calculate_zernikes=calculate_zernikes,
        shape_backend_provider=shape_backend_provider,
        zernike_backend_provider=zernike_backend_provider,
        regionprops_backend_provider=regionprops_backend_provider,
        feature_source_voxel_spacing=(
            labels.parent_image_source_voxel_spacing
            if isinstance(labels, ObjectLabelValue)
            else SourceVoxelSpacing()
        ),
    ).measurement_rows()
    runtime_profiler.log(
        "moss_total",
        time.perf_counter() - total_started_at,
        function="measure_object_size_shape",
        objects=len(measurement_rows),
    )
    return (image, measurement_rows)


class ObjectSizeShapeKernelPreparation(
    CellProfilerCallableKernelPreparation, metaclass=AutoRegisterMeta
):
    """Own the persistent kernel cache work for measure_object_size_shape."""

    def execute(self) -> None:
        """Compile AreaShape paths before benchmark execution."""
        image = np.linspace(0.0, 1.0, 32 * 32, dtype=np.float32).reshape((32, 32))
        labels = np.zeros((32, 32), dtype=np.int32)
        labels[8:24, 8:24] = 1
        measure_object_size_shape.__wrapped__(
            image,
            ObjectLabelPayload(
                variant_data=ObjectLabelVariantData(labels=labels),
                domain=ObjectLabelDomain(declared_object_ids=(1,)),
            ),
        )
        image_3d = np.linspace(0.0, 1.0, 8 * 16 * 16, dtype=np.float32).reshape(
            (8, 16, 16)
        )
        labels_3d = np.zeros(image_3d.shape, dtype=np.int32)
        labels_3d[1:4, 3:9, 3:9] = 1
        labels_3d[4:7, 7:14, 7:14] = 2
        measure_object_size_shape.__wrapped__(
            image_3d,
            ObjectLabelPayload(
                variant_data=ObjectLabelVariantData(labels=labels_3d),
                domain=ObjectLabelDomain(declared_object_ids=(1, 2)),
            ),
        )


measure_object_size_shape.__openhcs_prepare__ = (
    ObjectSizeShapeKernelPreparation().execute
)


@dataclass(frozen=True, slots=True)
class DenseObjectSizeShapeMeasurement(
    ObjectSizeShapeFeatureArrayOwner,
):
    """Size/shape measurement over nominally decomposed dense label planes."""

    owner_key = "dense_plane_stack"
    measurement_planes: tuple[ObjectLabelValue, ...]

    def rows(self) -> list[dict[str, object]]:
        rows: list[dict[str, object]] = []
        for slice_index, labels in enumerate(self.measurement_planes):
            rows.extend(
                self.slice_rows(
                    labels,
                    slice_index,
                )
            )
        return rows

    def slice_rows(
        self, labels: ObjectLabelValue, slice_index: int
    ) -> list[dict[str, object]]:
        labels_nd = object_label_dense_array(labels, dtype=np.int32)
        if not np.any(labels_nd > 0):
            return []
        feature_values, measured_labels, object_domain = self.feature_arrays_for_labels(
            labels_nd,
            object_domain=dense_object_label_measurement_row_domain(labels, labels_nd),
        )
        rows = ShapeObjectFeatureValueTable.from_feature_arrays(
            feature_values,
            measured_labels,
            object_domain=object_domain,
        ).rows()
        for row in rows:
            row[MeasurementRowAxisField.SLICE_INDEX.value] = int(slice_index)
        return rows


@dataclass(frozen=True, slots=True)
class SparseIJVObjectSizeShapeMeasurement(
    ObjectSizeShapeFeatureArrayOwner,
):
    """AreaShape rows for sparse IJV object-label payloads."""

    owner_key = "sparse_ijv"
    labels: ObjectLabelValue

    def rows(self) -> list[dict[str, object]]:
        sparse_rows = object_label_sparse_ijv_rows(self.labels)
        if sparse_rows.as_array().size == 0:
            return []
        if sparse_rows.has_slice_index:
            return self.slice_stack_rows(sparse_rows)
        return self.plane_rows(
            np.asarray(sparse_rows.as_yx_label_array(), dtype=np.int32)
        )

    def slice_stack_rows(
        self, sparse_rows: SparseIJVLabelRows
    ) -> list[dict[str, object]]:
        rows: list[dict[str, object]] = []
        slice_indices = sparse_rows.slice_indices()
        for slice_index in slice_indices:
            slice_ijv = np.asarray(
                sparse_rows.slice(slice_index).as_array(), dtype=np.int32
            )
            for row in self.plane_rows(slice_ijv):
                row[MeasurementRowAxisField.SLICE_INDEX.value] = int(slice_index)
                rows.append(row)
        return rows

    def plane_rows(self, ijv: np.ndarray) -> list[dict[str, object]]:
        object_ids = self.object_ids(ijv)
        rows: list[dict[str, object]] = []
        for object_id in object_ids:
            rows.append(self.object_row(ijv, int(object_id)))
        return rows

    def object_ids(self, ijv: np.ndarray) -> np.ndarray:
        return np.unique(ijv[:, 2]).astype(np.int32, copy=False)

    def object_row(self, ijv: np.ndarray, object_id: int) -> dict[str, object]:
        object_pixels = ijv[ijv[:, 2] == object_id]
        pixel_y = object_pixels[:, 0]
        pixel_x = object_pixels[:, 1]
        min_y = int(pixel_y.min())
        min_x = int(pixel_x.min())
        max_y = int(pixel_y.max()) + 1
        max_x = int(pixel_x.max()) + 1
        local = np.zeros((max_y - min_y, max_x - min_x), dtype=np.int32)
        local[pixel_y - min_y, pixel_x - min_x] = object_id
        feature_values, measured_labels, object_domain = self.feature_arrays_for_labels(
            local,
            object_domain=(object_id,),
        )
        ShapeCoordinateFeatureFields.apply_local_patch_offset(
            feature_values,
            local_offset_yx=(min_y, min_x),
        )
        return ShapeObjectFeatureValueTable.from_feature_arrays(
            feature_values,
            np.asarray([object_id], dtype=np.int32),
            object_domain=object_domain,
        ).rows()[0]


@dataclass(frozen=True, slots=True)
class ShapeCoordinateFeatureFields:
    """AreaShape feature fields whose values live in object-label XY coordinates."""

    @staticmethod
    def x_fields() -> tuple[str, ...]:
        return (
            _shape_feature(MeasureObjectSizeShapeModule.MeasurementFeature.CENTER_X),
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.BOUNDING_BOX_MINIMUM_X
            ),
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.BOUNDING_BOX_MAXIMUM_X
            ),
        )

    @staticmethod
    def y_fields() -> tuple[str, ...]:
        return (
            _shape_feature(MeasureObjectSizeShapeModule.MeasurementFeature.CENTER_Y),
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.BOUNDING_BOX_MINIMUM_Y
            ),
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.BOUNDING_BOX_MAXIMUM_Y
            ),
        )

    @classmethod
    def apply_local_patch_offset(
        cls,
        feature_values: dict[str, np.ndarray],
        *,
        local_offset_yx: tuple[int, int],
    ) -> None:
        """Restore coordinates removed by sparse per-object patch extraction."""
        offset_y, offset_x = (int(value) for value in local_offset_yx)
        if offset_x:
            for field in cls.x_fields():
                if field in feature_values:
                    feature_values[field] = (
                        np.asarray(feature_values[field], dtype=float) + offset_x
                    )
        if offset_y:
            for field in cls.y_fields():
                if field in feature_values:
                    feature_values[field] = (
                        np.asarray(feature_values[field], dtype=float) + offset_y
                    )


class ShapeMeasurementBackendStrategy(
    CellProfilerBackendStrategyMixin, ABC, metaclass=AutoRegisterMeta
):
    """Shape-measurement operations keyed by OpenHCS memory type/provider."""

    __registry_key__ = "backend_key"
    __skip_if_no_key__ = True

    @abstractmethod
    def form_factor_values(
        self, labels: np.ndarray, label_ids: np.ndarray
    ) -> np.ndarray:
        """Return CP-compatible AreaShape_FormFactor values."""

    @abstractmethod
    def radius_features_from_labels(
        self, labels: np.ndarray, label_ids: np.ndarray
    ) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
        """Return maximum, mean, and median object radii from dense labels."""

    @abstractmethod
    def feret_diameters(
        self, labels: np.ndarray, label_ids: np.ndarray
    ) -> tuple[np.ndarray, np.ndarray]:
        """Return minimum and maximum Feret diameters."""

    _unit_surface_triangles: ClassVar[np.ndarray | None] = None
    _cube_euler_coefficients: ClassVar[np.ndarray | None] = None

    def feature_arrays_3d(
        self,
        labels: np.ndarray,
        *,
        calculate_advanced: bool,
        spacing: tuple[float, ...],
    ) -> ShapeFeatureArrays:
        """Reference numerical owner for unprepared calls and oversized moments."""
        import skimage.measure

        regions = skimage.measure.regionprops(labels, cache=True)
        count = len(regions)
        measured_labels = np.empty(count, dtype=np.int64)
        area = np.empty(count, dtype=np.float64)
        centroid = np.empty((count, 3), dtype=np.float64)
        bounds = np.empty((count, 6), dtype=np.int64)
        eigenvalues = np.empty((count, 3), dtype=np.float64)
        euler_number = np.empty(count, dtype=np.int64)
        surface_areas = np.empty(count, dtype=np.float64)
        solidity = np.empty(count, dtype=np.float64) if calculate_advanced else None
        for index, region in enumerate(regions):
            measured_labels[index] = region.label
            area[index] = region.area
            centroid[index] = region.centroid
            bounds[index] = region.bbox
            eigenvalues[index] = region.inertia_tensor_eigvals
            euler_number[index] = region.euler_number
            lower = np.maximum(bounds[index, :3] - 1, 0)
            upper = np.minimum(bounds[index, 3:] + 1, labels.shape)
            binary = (
                labels[tuple(slice(a, b) for a, b in zip(lower, upper))] == region.label
            )
            surface_areas[index] = _surface_area(binary, spacing)
            if solidity is not None:
                solidity[index] = region.solidity
        return self._feature_arrays_from_3d_statistics(
            measured_labels,
            area,
            centroid,
            bounds,
            eigenvalues,
            euler_number,
            surface_areas,
            solidity,
        )

    @staticmethod
    def _feature_arrays_from_3d_statistics(
        measured_labels: np.ndarray,
        area: np.ndarray,
        centroid: np.ndarray,
        bounds: np.ndarray,
        inertia_tensor_eigenvalues: np.ndarray,
        euler_number: np.ndarray,
        surface_areas: np.ndarray,
        solidity: np.ndarray | None,
    ) -> ShapeFeatureArrays:
        """Retain the single declared AreaShape mapping for both algorithms."""
        bounding_box_volume = np.prod(bounds[:, 3:] - bounds[:, :3], axis=1).astype(
            np.float64
        )
        extent = area / bounding_box_volume
        equivalent_diameter = (6.0 * area / np.pi) ** (1.0 / 3.0)
        major_axis_length, minor_axis_length = _cellprofiler_3d_axis_lengths(
            inertia_tensor_eigenvalues
        )
        features = {
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.VOLUME
            ): area,
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.SURFACE_AREA
            ): surface_areas,
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.MAJOR_AXIS_LENGTH
            ): major_axis_length,
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.MINOR_AXIS_LENGTH
            ): minor_axis_length,
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.CENTER_X
            ): centroid[:, 2],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.CENTER_Y
            ): centroid[:, 1],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.CENTER_Z
            ): centroid[:, 0],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.BOUNDING_BOX_VOLUME
            ): bounding_box_volume,
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.BOUNDING_BOX_MINIMUM_X
            ): bounds[:, 2],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.BOUNDING_BOX_MAXIMUM_X
            ): bounds[:, 5],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.BOUNDING_BOX_MINIMUM_Y
            ): bounds[:, 1],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.BOUNDING_BOX_MAXIMUM_Y
            ): bounds[:, 4],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.BOUNDING_BOX_MINIMUM_Z
            ): bounds[:, 0],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.BOUNDING_BOX_MAXIMUM_Z
            ): bounds[:, 3],
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.EXTENT
            ): extent,
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.EULER_NUMBER
            ): euler_number,
            _shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.EQUIVALENT_DIAMETER
            ): equivalent_diameter,
        }
        if solidity is not None:
            features[
                _shape_feature(MeasureObjectSizeShapeModule.MeasurementFeature.SOLIDITY)
            ] = solidity
        return features, measured_labels

    @abstractmethod
    def distance_to_edge(self, labels: np.ndarray) -> np.ndarray:
        """Return per-pixel distance-to-edge for labeled objects."""

    @abstractmethod
    def maximum_position_of_labels(
        self,
        image: np.ndarray,
        labels: np.ndarray,
        label_ids: np.ndarray,
        *,
        mask: np.ndarray | None = None,
    ) -> tuple[np.ndarray, ...]:
        """Return maximum-value positions for each label."""

    @abstractmethod
    def color_labels(self, labels: np.ndarray) -> np.ndarray:
        """Return non-touching label color classes."""


class NumbaShapeMeasurementMixin(ABC):
    """Shared Numba-backed shape leaves reused by concrete backend policies."""

    def prepare_3d_shape_measurements(self) -> None:
        """Derive binary Lewiner geometry and warm both supported input layouts."""
        if ShapeMeasurementBackendStrategy._unit_surface_triangles is None:
            import skimage.measure
            from skimage.measure._regionprops_utils import EULER_COEFS3D_26

            triangles = []
            euler_coefficients = np.empty(256, dtype=np.int64)
            for case in range(256):
                cube = np.asarray(
                    [(case >> corner) & 1 for corner in range(8)],
                    dtype=np.float32,
                ).reshape((2, 2, 2))
                if case in (0, 255):
                    triangles.append(np.empty((0, 3, 3), dtype=np.float32))
                else:
                    vertices, faces, _normals, _values = skimage.measure.marching_cubes(
                        cube,
                        method="lewiner",
                        level=0,
                    )
                    triangles.append(vertices[faces])
                # Match the existing Euler convolution's reversed Z/Y/X
                # neighborhood and its X/Y bit ordering; retain its coefficients.
                euler_case = sum(
                    int(value) << corner
                    for corner, value in enumerate(
                        cube[::-1, ::-1, ::-1].transpose((0, 2, 1)).ravel()
                    )
                )
                euler_coefficients[case] = EULER_COEFS3D_26[euler_case]
            geometry = np.zeros(
                (len(triangles), max(map(len, triangles)), 3, 3), dtype=np.float32
            )
            for case, values in enumerate(triangles):
                geometry[case, : len(values)] = values
            geometry.setflags(write=False)
            euler_coefficients.setflags(write=False)
            ShapeMeasurementBackendStrategy._cube_euler_coefficients = (
                euler_coefficients
            )
            ShapeMeasurementBackendStrategy._unit_surface_triangles = geometry

        labels = np.zeros((3, 3, 3), dtype=np.int32)
        labels[1, 1, 1] = 1
        for writable in (True, False):
            labels.setflags(write=writable)
            self.feature_arrays_3d(
                labels, calculate_advanced=False, spacing=(1.0, 1.0, 1.0)
            )

    def feature_arrays_3d(
        self,
        labels: np.ndarray,
        *,
        calculate_advanced: bool,
        spacing: tuple[float, ...],
    ) -> ShapeFeatureArrays:
        """Measure the full label cohort without per-object binary meshes."""
        geometry = ShapeMeasurementBackendStrategy._unit_surface_triangles
        if geometry is None:
            # Direct public calls retain reference behavior before library READY.
            return super().feature_arrays_3d(
                labels, calculate_advanced=calculate_advanced, spacing=spacing
            )
        label_array = np.ascontiguousarray(labels, dtype=np.int32)
        label_ids = np.unique(label_array)
        label_ids = label_ids[label_ids > 0]
        counts, bounds = _label_bounds_counts_3d_numba(label_array, label_ids)
        if not self._local_moments_fit_int64(counts, bounds):
            return super().feature_arrays_3d(
                label_array, calculate_advanced=calculate_advanced, spacing=spacing
            )
        coefficients = ShapeMeasurementBackendStrategy._cube_euler_coefficients
        assert coefficients is not None
        sums, products, surface_cases, euler_scaled = (
            _label_local_moments_surface_euler_3d_numba(
                label_array, label_ids, bounds, coefficients
            )
        )
        area = counts.astype(np.float64)
        centroid = sums / area[:, None] + bounds[:, :3]
        inertia = np.zeros((label_ids.size, 3, 3), dtype=np.float64)
        for index, count in enumerate(counts):
            # Integer central numerators avoid subtracting large float moments.
            # Python integers also avoid overflow in the derived count products.
            n = int(count)
            local_sums = tuple(int(value) for value in sums[index])
            central = tuple(
                (n * int(products[index, product]) - local_sums[a] * local_sums[b])
                / (n * n)
                for product, (a, b) in enumerate(
                    ((0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (1, 2))
                )
            )
            inertia[index, 0, 0] = central[1] + central[2]
            inertia[index, 1, 1] = central[0] + central[2]
            inertia[index, 2, 2] = central[0] + central[1]
            inertia[index, 0, 1] = inertia[index, 1, 0] = -central[3]
            inertia[index, 0, 2] = inertia[index, 2, 0] = -central[4]
            inertia[index, 1, 2] = inertia[index, 2, 1] = -central[5]
        eigenvalues = np.maximum(np.linalg.eigvalsh(inertia)[:, ::-1], 0.0)
        if spacing == (1.0, 1.0, 1.0):
            vertices = geometry
        else:
            vertices = geometry * np.asarray(spacing, dtype=np.float64)
        edge_a = vertices[:, :, 0] - vertices[:, :, 1]
        edge_b = vertices[:, :, 0] - vertices[:, :, 2]
        case_areas = (
            np.sqrt((np.cross(edge_a, edge_b) ** 2).sum(axis=2)).sum(axis=1) / 2.0
        )
        surface_areas = surface_cases @ case_areas
        solidity = None
        if calculate_advanced:
            from skimage.morphology import convex_hull_image

            convex_volumes = np.empty(label_ids.size, dtype=np.int64)
            for index, label_id in enumerate(label_ids):
                lower, upper = bounds[index, :3], bounds[index, 3:]
                binary = (
                    label_array[tuple(slice(a, b) for a, b in zip(lower, upper))]
                    == label_id
                )
                convex_volumes[index] = np.count_nonzero(convex_hull_image(binary))
            solidity = area / convex_volumes
        return self._feature_arrays_from_3d_statistics(
            label_ids.astype(np.int64),
            area,
            centroid,
            bounds,
            eigenvalues,
            euler_scaled // 8,
            surface_areas,
            solidity,
        )

    @staticmethod
    def _local_moments_fit_int64(counts: np.ndarray, bounds: np.ndarray) -> bool:
        """Check one conservative bound before accumulating local moments."""
        capacity = np.iinfo(np.int64).max
        for count, region in zip(counts, bounds):
            extent = max(
                int(region[axis + 3]) - int(region[axis]) - 1 for axis in range(3)
            )
            if int(count) * extent * extent > capacity:
                return False
        return True

    def prepare_numba_shape_leaves(self) -> None:
        labels = np.array([[0, 1, 1], [0, 1, 0], [2, 2, 0]], dtype=np.int32)
        image = np.arange(9, dtype=np.float64).reshape((3, 3))
        label_ids = np.array([1, 2], dtype=np.int32)
        self.form_factor_values(labels, label_ids)
        self.radius_features_from_labels(labels, label_ids)
        self.feret_diameters(labels, label_ids)
        self.distance_to_edge(labels)
        for dtype in (np.float32, np.float64):
            ordering_image = image.astype(dtype)
            _numpy124_aquicksort_indices(ordering_image.ravel())
            self.maximum_position_of_labels(ordering_image, labels, label_ids)
            immutable_ids = label_ids.view()
            immutable_ids.setflags(write=False)
            self.maximum_position_of_labels(ordering_image, labels, immutable_ids)
        self.color_labels(labels)
        self.prepare_3d_shape_measurements()

    def form_factor_values(
        self, labels: np.ndarray, label_ids: np.ndarray
    ) -> np.ndarray:
        return _form_factor_values_from_labels(
            np.asarray(labels, dtype=np.int32), np.asarray(label_ids, dtype=np.int32)
        )

    def radius_features_from_labels(
        self, labels: np.ndarray, label_ids: np.ndarray
    ) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
        return _radius_features_from_labels_numba(
            np.asarray(labels, dtype=np.int32), np.asarray(label_ids, dtype=np.int32)
        )

    def distance_to_edge(self, labels: np.ndarray) -> np.ndarray:
        label_array = np.asarray(labels, dtype=np.int32)
        if label_array.ndim != 2:
            return _distance_to_edge_planewise(self, label_array)
        return _distance_to_label_edge_numba(np.ascontiguousarray(label_array))

    def maximum_position_of_labels(
        self,
        image: np.ndarray,
        labels: np.ndarray,
        label_ids: np.ndarray,
        *,
        mask: np.ndarray | None = None,
    ) -> tuple[np.ndarray, ...]:
        return _maximum_position_of_labels_scipy_select(
            np.asarray(image),
            np.asarray(labels, dtype=np.int32),
            np.asarray(label_ids, dtype=np.int32),
            mask=mask,
        )

    def color_labels(self, labels: np.ndarray) -> np.ndarray:
        return _color_labels_numpy(np.asarray(labels, dtype=np.int32))

    def feret_diameters(
        self, labels: np.ndarray, label_ids: np.ndarray
    ) -> tuple[np.ndarray, np.ndarray]:
        return feret_diameters_from_labels(labels, label_ids)


class LegacyFastNumpyShapeMeasurementBackendStrategy(
    NumbaShapeMeasurementMixin, ShapeMeasurementBackendStrategy
):
    """Default NumPy shape backend with native leaves and explicit gaps."""

    backend_key = CellProfilerBackendAuthority.backend_key(
        MemoryType.NUMPY, CellProfilerBackendProvider.LEGACY_FAST
    )
    memory_type = MemoryType.NUMPY
    backend_provider = CellProfilerBackendProvider.LEGACY_FAST
    is_default_backend = True

    def prepare_backend(self) -> None:
        self.prepare_numba_shape_leaves()


class NumbaNumpyShapeMeasurementBackendStrategy(
    NumbaShapeMeasurementMixin, ShapeMeasurementBackendStrategy
):
    """Pure Numba shape backend. Unsupported leaves fail explicitly."""

    backend_key = CellProfilerBackendAuthority.backend_key(
        MemoryType.NUMPY, CellProfilerBackendProvider.NUMBA
    )
    memory_type = MemoryType.NUMPY
    backend_provider = CellProfilerBackendProvider.NUMBA
    is_default_backend = False

    def prepare_backend(self) -> None:
        self.prepare_numba_shape_leaves()


def _distance_to_edge_planewise(
    backend: ShapeMeasurementBackendStrategy, labels: np.ndarray
) -> np.ndarray:
    if labels.ndim < 2:
        raise ValueError("Distance-to-edge requires at least two dimensions.")
    distances = np.empty(labels.shape, dtype=np.float64)
    plane_count = int(np.prod(labels.shape[:-2], dtype=np.int64))
    source_planes = labels.reshape((plane_count, *labels.shape[-2:]))
    target_planes = distances.reshape((plane_count, *labels.shape[-2:]))
    for plane_index in range(plane_count):
        target_planes[plane_index] = backend.distance_to_edge(
            source_planes[plane_index]
        )
    return distances


def shape_measurement_backend(
    *, backend_provider: BackendProviderInput = DEFAULT_CELLPROFILER_BACKEND_SELECTION
) -> ShapeMeasurementBackendStrategy:
    """Return the selected shape-measurement backend."""
    return ShapeMeasurementBackendStrategy.for_memory_type(
        MemoryType.NUMPY, backend_provider=backend_provider
    )


def form_factor_values(
    labels: np.ndarray,
    label_ids: np.ndarray,
    *,
    backend_provider: BackendProviderInput = DEFAULT_CELLPROFILER_BACKEND_SELECTION,
) -> np.ndarray:
    """Return CP-compatible AreaShape_FormFactor values through a backend."""
    return ShapeMeasurementBackendStrategy.for_memory_type(
        MemoryType.NUMPY, backend_provider=backend_provider
    ).form_factor_values(labels, label_ids)


def _convex_area_and_solidity_from_labels(
    labels: np.ndarray, region_props: object
) -> tuple[np.ndarray, np.ndarray]:
    """Return exact skimage-compatible convex area and solidity per label."""
    morphology_backend = MorphologyBackendStrategy.for_memory_type(MemoryType.NUMPY)
    object_count = int(region_props.label.size)
    convex_area = np.zeros(object_count, dtype=float)
    solidity = np.ones(object_count, dtype=float)
    for index, label_id in enumerate(region_props.label):
        min_y = int(region_props.bbox_min_y[index])
        min_x = int(region_props.bbox_min_x[index])
        max_y = int(region_props.bbox_max_y[index])
        max_x = int(region_props.bbox_max_x[index])
        crop = labels[min_y:max_y, min_x:max_x] == int(label_id)
        hull = morphology_backend.convex_hull_image(crop)
        hull_area = float(np.count_nonzero(hull))
        convex_area[index] = hull_area
        solidity[index] = (
            float(region_props.area[index]) / hull_area if hull_area > 0.0 else np.nan
        )
    return (convex_area, solidity)


def _desired_region_properties(dimensions: int, calculate_advanced: bool) -> list[str]:
    if dimensions == 2:
        properties = [
            "label",
            "image",
            "area",
            "perimeter",
            "bbox",
            "bbox_area",
            "major_axis_length",
            "minor_axis_length",
            "orientation",
            "centroid",
            "equivalent_diameter",
            "extent",
            "eccentricity",
            "convex_area",
            "solidity",
            "euler_number",
        ]
        if calculate_advanced:
            properties.extend(
                [
                    "inertia_tensor",
                    "inertia_tensor_eigvals",
                    "moments",
                    "moments_central",
                    "moments_hu",
                    "moments_normalized",
                ]
            )
        return properties
    properties = [
        "label",
        "image",
        "area",
        "centroid",
        "bbox",
        "bbox_area",
        "inertia_tensor_eigvals",
        "extent",
        "equivalent_diameter",
        "euler_number",
    ]
    if calculate_advanced:
        properties.append("solidity")
    return properties


def _shape_feature(feature: MeasureObjectSizeShapeModule.MeasurementFeature) -> str:
    return feature.value


def _indexed_shape_feature(
    feature: MeasureObjectSizeShapeModule.MeasurementFeature, *indices: int
) -> str:
    return feature.indexed_name(*indices)


def _advanced_2d_features(props: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    features: dict[str, np.ndarray] = {}
    for row in range(3):
        for column in range(4):
            features[
                _indexed_shape_feature(
                    MeasureObjectSizeShapeModule.MeasurementFeature.SPATIAL_MOMENT,
                    row,
                    column,
                )
            ] = props[f"moments-{row}-{column}"]
            features[
                _indexed_shape_feature(
                    MeasureObjectSizeShapeModule.MeasurementFeature.CENTRAL_MOMENT,
                    row,
                    column,
                )
            ] = props[f"moments_central-{row}-{column}"]
    for row in range(4):
        for column in range(4):
            features[
                _indexed_shape_feature(
                    MeasureObjectSizeShapeModule.MeasurementFeature.NORMALIZED_MOMENT,
                    row,
                    column,
                )
            ] = props[f"moments_normalized-{row}-{column}"]
    for index in range(7):
        features[
            _indexed_shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.HU_MOMENT, index
            )
        ] = props[f"moments_hu-{index}"]
    for row in range(2):
        for column in range(2):
            features[
                _indexed_shape_feature(
                    MeasureObjectSizeShapeModule.MeasurementFeature.INERTIA_TENSOR,
                    row,
                    column,
                )
            ] = props[f"inertia_tensor-{row}-{column}"]
    for index in range(2):
        features[
            _indexed_shape_feature(
                MeasureObjectSizeShapeModule.MeasurementFeature.INERTIA_TENSOR_EIGENVALUES,
                index,
            )
        ] = props[f"inertia_tensor_eigvals-{index}"]
    return features


def _cellprofiler_3d_axis_lengths(
    inertia_tensor_eigenvalues: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    """Return CellProfiler-compatible 3-D AreaShape axis lengths."""
    return (
        4.0 * np.sqrt(np.maximum(inertia_tensor_eigenvalues[:, 0], 0.0)),
        4.0 * np.sqrt(np.maximum(inertia_tensor_eigenvalues[:, 2], 0.0)),
    )


def _zernike_features(
    labels: np.ndarray,
    measured_labels: np.ndarray,
    *,
    backend_provider: BackendProviderInput,
) -> dict[str, np.ndarray]:
    zernike_numbers, zernike_values = shape_zernike_moments(
        labels,
        measured_labels,
        max_order=MeasureObjectSizeShapeModule.zernike_max_order,
        backend_provider=backend_provider,
    )
    return {
        MeasureObjectSizeShapeModule.shape_zernike_feature_name(
            degree=int(n), repetition=int(m)
        ): values
        for (n, m), values in zip(zernike_numbers, zernike_values.transpose())
    }


@njit(cache=True)
def _label_bounds_counts_3d_numba(
    labels: np.ndarray, label_ids: np.ndarray
) -> tuple[np.ndarray, np.ndarray]:
    """First cohort pass captures bounds for stable local moment coordinates."""
    nz, ny, nx = labels.shape
    counts = np.zeros(label_ids.size, dtype=np.int64)
    bounds = np.zeros((label_ids.size, 6), dtype=np.int64)
    bounds[:, 0] = nz
    bounds[:, 1] = ny
    bounds[:, 2] = nx
    for z in range(nz):
        for y in range(ny):
            for x in range(nx):
                label = labels[z, y, x]
                if label <= 0:
                    continue
                index = np.searchsorted(label_ids, label)
                counts[index] += 1
                bounds[index, 0] = min(bounds[index, 0], z)
                bounds[index, 1] = min(bounds[index, 1], y)
                bounds[index, 2] = min(bounds[index, 2], x)
                bounds[index, 3] = max(bounds[index, 3], z + 1)
                bounds[index, 4] = max(bounds[index, 4], y + 1)
                bounds[index, 5] = max(bounds[index, 5], x + 1)
    return counts, bounds


@njit(cache=True)
def _label_local_moments_surface_euler_3d_numba(
    labels: np.ndarray,
    label_ids: np.ndarray,
    bounds: np.ndarray,
    euler_coefficients: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """Second cohort pass collects local moments and correlated cube counts."""
    count = label_ids.size
    sums = np.zeros((count, 3), dtype=np.int64)
    products = np.zeros((count, 6), dtype=np.int64)
    surface_cases = np.zeros((count, 256), dtype=np.int64)
    euler_scaled = np.zeros(count, dtype=np.int64)
    corners = np.zeros(8, dtype=np.int32)
    nz, ny, nx = labels.shape
    for z in range(-1, nz):
        for y in range(-1, ny):
            for x in range(-1, nx):
                for corner in range(8):
                    zz = z + (corner >> 2)
                    yy = y + ((corner >> 1) & 1)
                    xx = x + (corner & 1)
                    if 0 <= zz < nz and 0 <= yy < ny and 0 <= xx < nx:
                        corners[corner] = labels[zz, yy, xx]
                    else:
                        corners[corner] = 0
                if corners[0] > 0:
                    index = np.searchsorted(label_ids, corners[0])
                    local_z = z - bounds[index, 0]
                    local_y = y - bounds[index, 1]
                    local_x = x - bounds[index, 2]
                    sums[index, 0] += local_z
                    sums[index, 1] += local_y
                    sums[index, 2] += local_x
                    products[index, 0] += local_z * local_z
                    products[index, 1] += local_y * local_y
                    products[index, 2] += local_x * local_x
                    products[index, 3] += local_z * local_y
                    products[index, 4] += local_z * local_x
                    products[index, 5] += local_y * local_x
                if (
                    corners[0]
                    == corners[1]
                    == corners[2]
                    == corners[3]
                    == corners[4]
                    == corners[5]
                    == corners[6]
                    == corners[7]
                ):
                    continue
                for corner in range(8):
                    label = corners[corner]
                    if label <= 0:
                        continue
                    seen = False
                    for previous in range(corner):
                        if corners[previous] == label:
                            seen = True
                    if seen:
                        continue
                    case = 0
                    for other in range(8):
                        if corners[other] == label:
                            case |= 1 << other
                    index = np.searchsorted(label_ids, label)
                    euler_scaled[index] += euler_coefficients[case]
                    # Euler includes an exterior zero border; marching cubes
                    # retains the original clipped domain, including open edges.
                    if 0 <= z < nz - 1 and 0 <= y < ny - 1 and 0 <= x < nx - 1:
                        surface_cases[index, case] += 1
    return sums, products, surface_cases, euler_scaled


def _surface_area(
    volume: np.ndarray, spacing: tuple[float, ...] | None = None
) -> float:
    import skimage.measure

    if not np.any(volume):
        return 0.0
    if spacing is None:
        spacing = (1.0,) * volume.ndim
    try:
        verts, faces, _normals, _values = skimage.measure.marching_cubes(
            volume, method="lewiner", spacing=spacing, level=0
        )
    except ValueError:
        return 0.0
    edge_a = verts[faces[:, 0]] - verts[faces[:, 1]]
    edge_b = verts[faces[:, 0]] - verts[faces[:, 2]]
    return float(((np.cross(edge_a, edge_b) ** 2).sum(axis=1) ** 0.5).sum() / 2.0)


def _form_factor_values_from_labels(
    labels: np.ndarray, label_ids: np.ndarray
) -> np.ndarray:
    label_array = np.asarray(labels, dtype=np.int32)
    label_id_array = np.asarray(label_ids, dtype=np.int32)
    if label_id_array.size == 0:
        return np.zeros(0, dtype=np.float64)
    if label_array.ndim != 2:
        raise ValueError(
            f"Form-factor values require 2-D labels, got {label_array.ndim}D."
        )
    properties = LabelRegionPropertiesBackendStrategy.for_memory_type().measure_2d(
        label_array, include_advanced=False
    )
    max_label = int(max(label_id_array.max(initial=0), properties.label.max(initial=0)))
    areas_by_label = np.zeros(max_label + 1, dtype=np.float64)
    perimeters_by_label = np.zeros(max_label + 1, dtype=np.float64)
    if properties.label.size:
        areas_by_label[properties.label.astype(np.int32, copy=False)] = properties.area
        perimeters_by_label[properties.label.astype(np.int32, copy=False)] = (
            properties.perimeter
        )
    valid = (label_id_array > 0) & (label_id_array <= max_label)
    areas = np.zeros(label_id_array.size, dtype=np.float64)
    perimeters = np.zeros(label_id_array.size, dtype=np.float64)
    areas[valid] = areas_by_label[label_id_array[valid]]
    perimeters[valid] = perimeters_by_label[label_id_array[valid]]
    with np.errstate(divide="ignore", invalid="ignore"):
        return 4.0 * np.pi * areas / perimeters**2


def _first_scalar(value: object) -> float:
    array = np.asarray(value)
    if array.size == 0:
        return 0.0
    return float(array.reshape(-1)[0])


@njit(cache=True)
def _radius_features_from_distance_image_numba(
    labels: np.ndarray, distances: np.ndarray, label_ids: np.ndarray
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    object_count = label_ids.size
    max_label = 0
    for i in range(object_count):
        label_id = int(label_ids[i])
        if label_id > max_label:
            max_label = label_id
    counts_by_label = np.zeros(max_label + 1, dtype=np.int64)
    sums_by_label = np.zeros(max_label + 1, dtype=np.float64)
    max_by_label = np.zeros(max_label + 1, dtype=np.float64)
    rows, cols = labels.shape
    for row in range(rows):
        for col in range(cols):
            label = int(labels[row, col])
            if label > 0 and label <= max_label:
                value = distances[row, col]
                counts_by_label[label] += 1
                sums_by_label[label] += value
                if value > max_by_label[label]:
                    max_by_label[label] = value
    offsets = np.zeros(max_label + 2, dtype=np.int64)
    for label in range(max_label + 1):
        offsets[label + 1] = offsets[label] + counts_by_label[label]
    cursor = offsets.copy()
    ordered = np.empty(offsets[max_label + 1], dtype=np.float64)
    for row in range(rows):
        for col in range(cols):
            label = int(labels[row, col])
            if label > 0 and label <= max_label:
                index = cursor[label]
                ordered[index] = distances[row, col]
                cursor[label] = index + 1
    max_radius = np.zeros(object_count, dtype=np.float64)
    mean_radius = np.zeros(object_count, dtype=np.float64)
    median_radius = np.zeros(object_count, dtype=np.float64)
    for i in range(object_count):
        label = int(label_ids[i])
        if label <= 0 or label > max_label:
            continue
        count = counts_by_label[label]
        if count <= 0:
            continue
        start = offsets[label]
        values = ordered[start : start + count].copy()
        values.sort()
        max_radius[i] = max_by_label[label]
        mean_radius[i] = sums_by_label[label] / count
        middle = count // 2
        if count % 2 == 1:
            median_radius[i] = values[middle]
        else:
            median_radius[i] = 0.5 * (values[middle - 1] + values[middle])
    return (max_radius, mean_radius, median_radius)


@njit(cache=True)
def _radius_features_from_labels_numba(
    labels: np.ndarray, label_ids: np.ndarray
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    object_count = label_ids.size
    max_label = 0
    for i in range(object_count):
        label_id = int(label_ids[i])
        if label_id > max_label:
            max_label = label_id
    height, width = labels.shape
    min_y = np.full(max_label + 1, height, dtype=np.int64)
    min_x = np.full(max_label + 1, width, dtype=np.int64)
    max_y = np.zeros(max_label + 1, dtype=np.int64)
    max_x = np.zeros(max_label + 1, dtype=np.int64)
    counts = np.zeros(max_label + 1, dtype=np.int64)
    for y in range(height):
        for x in range(width):
            label = int(labels[y, x])
            if label <= 0 or label > max_label:
                continue
            counts[label] += 1
            if y < min_y[label]:
                min_y[label] = y
            if x < min_x[label]:
                min_x[label] = x
            if y + 1 > max_y[label]:
                max_y[label] = y + 1
            if x + 1 > max_x[label]:
                max_x[label] = x + 1
    max_radius = np.zeros(object_count, dtype=np.float64)
    mean_radius = np.zeros(object_count, dtype=np.float64)
    median_radius = np.zeros(object_count, dtype=np.float64)
    inf = 1e20
    for object_index in range(object_count):
        label = int(label_ids[object_index])
        if label <= 0 or label > max_label or counts[label] <= 0:
            continue
        crop_height = max_y[label] - min_y[label] + 2
        crop_width = max_x[label] - min_x[label] + 2
        row_distances = np.empty((crop_height, crop_width), dtype=np.float64)
        distances_sq = np.empty((crop_height, crop_width), dtype=np.float64)
        for yy in range(crop_height):
            source = np.empty(crop_width, dtype=np.float64)
            source_y = min_y[label] + yy - 1
            for xx in range(crop_width):
                source_x = min_x[label] + xx - 1
                if (
                    source_y >= 0
                    and source_y < height
                    and (source_x >= 0)
                    and (source_x < width)
                    and (labels[source_y, source_x] == label)
                ):
                    source[xx] = inf
                else:
                    source[xx] = 0.0
            row_output = np.empty(crop_width, dtype=np.float64)
            row_arg = np.empty(crop_width, dtype=np.int64)
            _edt_1d_numba(source, row_output, row_arg)
            for xx in range(crop_width):
                row_distances[yy, xx] = row_output[xx]
        for xx in range(crop_width):
            source = np.empty(crop_height, dtype=np.float64)
            for yy in range(crop_height):
                source[yy] = row_distances[yy, xx]
            column_output = np.empty(crop_height, dtype=np.float64)
            column_arg = np.empty(crop_height, dtype=np.int64)
            _edt_1d_numba(source, column_output, column_arg)
            for yy in range(crop_height):
                distances_sq[yy, xx] = column_output[yy]
        object_pixel_count = counts[label]
        values = np.empty(object_pixel_count, dtype=np.float64)
        value_index = 0
        total = 0.0
        maximum = 0.0
        for yy in range(1, crop_height - 1):
            source_y = min_y[label] + yy - 1
            for xx in range(1, crop_width - 1):
                source_x = min_x[label] + xx - 1
                if labels[source_y, source_x] != label:
                    continue
                value = np.sqrt(distances_sq[yy, xx])
                values[value_index] = value
                value_index += 1
                total += value
                if value > maximum:
                    maximum = value
        values.sort()
        middle = object_pixel_count // 2
        max_radius[object_index] = maximum
        mean_radius[object_index] = total / object_pixel_count
        if object_pixel_count % 2 == 1:
            median_radius[object_index] = values[middle]
        else:
            median_radius[object_index] = 0.5 * (values[middle - 1] + values[middle])
    return (max_radius, mean_radius, median_radius)


@njit(cache=True)
def _distance_to_label_edge_numba(labels: np.ndarray) -> np.ndarray:
    height, width = labels.shape
    max_label = 0
    for y in range(height):
        for x in range(width):
            label = int(labels[y, x])
            if label > max_label:
                max_label = label
    output = np.zeros((height, width), dtype=np.float64)
    if max_label <= 0:
        return output
    min_y = np.full(max_label + 1, height, dtype=np.int64)
    min_x = np.full(max_label + 1, width, dtype=np.int64)
    max_y = np.zeros(max_label + 1, dtype=np.int64)
    max_x = np.zeros(max_label + 1, dtype=np.int64)
    counts = np.zeros(max_label + 1, dtype=np.int64)
    for y in range(height):
        for x in range(width):
            label = int(labels[y, x])
            if label <= 0:
                continue
            counts[label] += 1
            if y < min_y[label]:
                min_y[label] = y
            if x < min_x[label]:
                min_x[label] = x
            if y + 1 > max_y[label]:
                max_y[label] = y + 1
            if x + 1 > max_x[label]:
                max_x[label] = x + 1
    inf = 1e20
    for label in range(1, max_label + 1):
        if counts[label] <= 0:
            continue
        crop_y0 = min_y[label] - 1
        if crop_y0 < 0:
            crop_y0 = 0
        crop_x0 = min_x[label] - 1
        if crop_x0 < 0:
            crop_x0 = 0
        crop_y1 = max_y[label] + 1
        if crop_y1 > height:
            crop_y1 = height
        crop_x1 = max_x[label] + 1
        if crop_x1 > width:
            crop_x1 = width
        crop_height = crop_y1 - crop_y0
        crop_width = crop_x1 - crop_x0
        has_background = False
        for yy in range(crop_height):
            source_y = crop_y0 + yy
            for xx in range(crop_width):
                source_x = crop_x0 + xx
                if labels[source_y, source_x] != label:
                    has_background = True
                    break
            if has_background:
                break
        if not has_background:
            for yy in range(crop_height):
                source_y = crop_y0 + yy
                y_distance = yy + 1
                for xx in range(crop_width):
                    source_x = crop_x0 + xx
                    output[source_y, source_x] = np.sqrt(
                        y_distance * y_distance + xx * xx
                    )
            continue
        row_distances = np.empty((crop_height, crop_width), dtype=np.float64)
        distances_sq = np.empty((crop_height, crop_width), dtype=np.float64)
        for yy in range(crop_height):
            source = np.empty(crop_width, dtype=np.float64)
            source_y = crop_y0 + yy
            for xx in range(crop_width):
                source_x = crop_x0 + xx
                if labels[source_y, source_x] == label:
                    source[xx] = inf
                else:
                    source[xx] = 0.0
            row_output = np.empty(crop_width, dtype=np.float64)
            row_arg = np.empty(crop_width, dtype=np.int64)
            _edt_1d_numba(source, row_output, row_arg)
            for xx in range(crop_width):
                row_distances[yy, xx] = row_output[xx]
        for xx in range(crop_width):
            source = np.empty(crop_height, dtype=np.float64)
            for yy in range(crop_height):
                source[yy] = row_distances[yy, xx]
            column_output = np.empty(crop_height, dtype=np.float64)
            column_arg = np.empty(crop_height, dtype=np.int64)
            _edt_1d_numba(source, column_output, column_arg)
            for yy in range(crop_height):
                distances_sq[yy, xx] = column_output[yy]
        for yy in range(crop_height):
            source_y = crop_y0 + yy
            for xx in range(crop_width):
                source_x = crop_x0 + xx
                if labels[source_y, source_x] == label:
                    output[source_y, source_x] = np.sqrt(distances_sq[yy, xx])
    return output


@njit(cache=True)
def _maximum_position_of_labels_numba(
    image: np.ndarray, labels: np.ndarray, label_ids: np.ndarray
) -> tuple[np.ndarray, np.ndarray]:
    object_count = label_ids.size
    max_label = 0
    for index in range(object_count):
        label = int(label_ids[index])
        if label > max_label:
            max_label = label
    best_values = np.full(max_label + 1, -np.inf, dtype=np.float64)
    best_y = np.full(max_label + 1, -1, dtype=np.int64)
    best_x = np.full(max_label + 1, -1, dtype=np.int64)
    seen = np.zeros(max_label + 1, dtype=np.bool_)
    height, width = labels.shape
    for y in range(height):
        for x in range(width):
            label = int(labels[y, x])
            if label <= 0 or label > max_label:
                continue
            value = image[y, x]
            if not seen[label] or value > best_values[label]:
                seen[label] = True
                best_values[label] = value
                best_y[label] = y
                best_x[label] = x
    centers_i = np.zeros(object_count, dtype=np.float64)
    centers_j = np.zeros(object_count, dtype=np.float64)
    for index in range(object_count):
        label = int(label_ids[index])
        if label > 0 and label <= max_label and seen[label]:
            centers_i[index] = float(best_y[label])
            centers_j[index] = float(best_x[label])
    return (centers_i, centers_j)


def _maximum_position_of_labels_scipy_select(
    image: np.ndarray,
    labels: np.ndarray,
    label_ids: np.ndarray,
    *,
    mask: np.ndarray | None = None,
) -> tuple[np.ndarray, ...]:
    """Return maximum positions using CellProfiler 4.2 labeled tie semantics."""
    image_array = np.asarray(image)
    label_array = np.asarray(labels, dtype=np.int32)
    label_id_array = np.asarray(label_ids, dtype=np.int32)
    if image_array.shape != label_array.shape:
        raise ValueError(
            f"Maximum-position image and labels must have matching shapes; got {image_array.shape!r} and {label_array.shape!r}."
        )
    if label_id_array.size == 0:
        return tuple(np.zeros(0, dtype=np.float64) for _axis in range(image_array.ndim))
    if mask is None:
        source_positions = np.arange(image_array.size, dtype=np.int64)
    else:
        mask_array = np.asarray(mask, dtype=bool)
        if mask_array.shape != image_array.shape:
            raise ValueError(
                "Maximum-position mask must match the image domain; got "
                f"{mask_array.shape!r} and {image_array.shape!r}."
            )
        source_positions = np.flatnonzero(mask_array.ravel())
    max_label = int(np.max(label_array)) if label_array.size else 0
    working_values = image_array.ravel()[source_positions]
    working_labels = label_array.ravel()[source_positions]
    order = _numpy124_ordered_label_maximum_indices(
        working_values, working_labels, label_id_array.ravel(), max_label
    )
    sorted_labels = working_labels[order]
    sorted_positions = source_positions[order]
    max_positions = np.zeros(max_label + 2, dtype=np.int64)
    valid_sorted = (sorted_labels >= 0) & (sorted_labels <= max_label)
    valid_sorted_labels = sorted_labels[valid_sorted]
    valid_sorted_positions = sorted_positions[valid_sorted]
    max_positions[valid_sorted_labels] = valid_sorted_positions
    safe_label_ids = np.zeros(label_id_array.shape, dtype=np.int64)
    present = (label_id_array >= 0) & (label_id_array <= max_label)
    safe_label_ids[present] = label_id_array[present]
    selected_positions = max_positions[safe_label_ids]
    return tuple(
        np.asarray(coordinates, dtype=np.float64)
        for coordinates in np.unravel_index(selected_positions, image_array.shape)
    )


def _color_labels_numpy(labels: np.ndarray) -> np.ndarray:
    """Return CP-compatible non-touching label color classes."""
    label_array = np.asarray(labels, dtype=np.int32)
    if label_array.size == 0:
        return np.zeros(label_array.shape, dtype=int)
    if not _has_touching_foreground_labels_numba(np.ascontiguousarray(label_array)):
        return (label_array != 0).astype(int)
    neighbor_counts, neighbor_starts, neighbor_labels = _find_label_neighbors_numpy(
        label_array
    )
    colors_by_label = np.zeros(neighbor_counts.size + 1, dtype=int)
    if neighbor_counts.size == 0:
        return colors_by_label[label_array]
    isolated_labels = neighbor_counts == 0
    if np.all(isolated_labels):
        return (label_array != 0).astype(int)
    colors_by_label[1:][isolated_labels] = 1
    connected_counts = neighbor_counts[~isolated_labels]
    connected_starts = neighbor_starts[~isolated_labels]
    connected_labels = np.flatnonzero(~isolated_labels) + 1
    sort_order = np.lexsort((-connected_counts,))
    connected_counts = connected_counts[sort_order]
    connected_starts = connected_starts[sort_order]
    connected_labels = connected_labels[sort_order]
    for index in range(connected_counts.size):
        start = int(connected_starts[index])
        end = start + int(connected_counts[index])
        neighbor_colors = np.unique(colors_by_label[neighbor_labels[start:end]])
        if neighbor_colors.size == 1 and neighbor_colors[0] == 0:
            colors_by_label[connected_labels[index]] = 1
            continue
        if neighbor_colors[0] == 0:
            neighbor_colors = neighbor_colors[1:]
        expected_colors = np.arange(1, neighbor_colors.size + 1)
        missing_color_positions = expected_colors[neighbor_colors != expected_colors]
        if missing_color_positions.size:
            colors_by_label[connected_labels[index]] = int(missing_color_positions[0])
        else:
            colors_by_label[connected_labels[index]] = int(neighbor_colors.size + 1)
    return colors_by_label[label_array]


@njit(cache=True)
def _has_touching_foreground_labels_numba(labels: np.ndarray) -> bool:
    height, width = labels.shape
    for y in range(height):
        for x in range(width):
            label = labels[y, x]
            if label <= 0:
                continue
            if x + 1 < width:
                neighbor = labels[y, x + 1]
                if neighbor > 0 and neighbor != label:
                    return True
            if y + 1 < height:
                neighbor = labels[y + 1, x]
                if neighbor > 0 and neighbor != label:
                    return True
                if x + 1 < width:
                    neighbor = labels[y + 1, x + 1]
                    if neighbor > 0 and neighbor != label:
                        return True
                if x > 0:
                    neighbor = labels[y + 1, x - 1]
                    if neighbor > 0 and neighbor != label:
                        return True
    return False


def _find_label_neighbors_numpy(
    labels: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Return per-label 8-connected neighboring label lists."""
    label_array = np.asarray(labels, dtype=np.int32)
    if label_array.size == 0:
        return (np.zeros(0, dtype=int), np.zeros(0, dtype=int), np.zeros(0, dtype=int))
    max_label = int(np.max(label_array))
    padded = np.zeros(np.asarray(label_array.shape) + 2, dtype=np.int32)
    padded[1:-1, 1:-1] = label_array
    adjacent_y, adjacent_x = np.argwhere(_adjacent_label_mask_numpy(padded)).transpose()
    if adjacent_y.size == 0:
        return (
            np.zeros(max_label, dtype=int),
            np.zeros(max_label, dtype=int),
            np.zeros(0, dtype=int),
        )
    repeated_labels = np.hstack([padded[adjacent_y, adjacent_x]] * 8)
    neighbor_values = np.zeros(adjacent_y.size * 8, dtype=int)
    offset = 0
    for dy, dx in (
        (-1, -1),
        (-1, 0),
        (-1, 1),
        (0, -1),
        (0, 1),
        (1, -1),
        (1, 0),
        (1, 1),
    ):
        neighbor_values[offset : offset + adjacent_y.size] = padded[
            adjacent_y + dy, adjacent_x + dx
        ]
        offset += adjacent_y.size
    sort_order = np.lexsort((neighbor_values, repeated_labels))
    repeated_labels = repeated_labels[sort_order]
    neighbor_values = neighbor_values[sort_order]
    first_occurrence = np.ones(repeated_labels.size, dtype=bool)
    first_occurrence[1:] = (repeated_labels[1:] != repeated_labels[:-1]) | (
        neighbor_values[1:] != neighbor_values[:-1]
    )
    repeated_labels = repeated_labels[first_occurrence]
    neighbor_values = neighbor_values[first_occurrence]
    keep = (repeated_labels != neighbor_values) & (neighbor_values != 0)
    repeated_labels = repeated_labels[keep]
    neighbor_values = neighbor_values[keep]
    neighbor_counts = np.bincount(repeated_labels, minlength=max_label + 1)[1:].astype(
        int
    )
    neighbor_starts = np.cumsum(neighbor_counts)
    if neighbor_starts.size:
        neighbor_starts[1:] = neighbor_starts[:-1]
        neighbor_starts[0] = 0
    return (neighbor_counts, neighbor_starts, neighbor_values)


def _adjacent_label_mask_numpy(labels: np.ndarray) -> np.ndarray:
    """Return foreground labels touching a different 8-connected label."""
    import scipy.ndimage

    label_array = labels.astype(np.int32, copy=False)
    high = int(label_array.max()) + 1 if label_array.size else 1
    image_with_high_background = label_array.copy()
    image_with_high_background[label_array == 0] = high
    footprint = np.ones((3, 3), dtype=bool)
    minimum_label = scipy.ndimage.minimum_filter(
        image_with_high_background, footprint=footprint, mode="constant", cval=high
    )
    maximum_label = scipy.ndimage.maximum_filter(
        label_array, footprint=footprint, mode="constant", cval=0
    )
    return (minimum_label != maximum_label) & (label_array > 0)


__all__ = [
    "LegacyFastNumpyShapeMeasurementBackendStrategy",
    "NumbaNumpyShapeMeasurementBackendStrategy",
    "ShapeMeasurementBackendStrategy",
    "form_factor_values",
    "shape_measurement_backend",
]
