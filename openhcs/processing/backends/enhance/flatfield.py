"""Nominal contracts shared by flat-field correction implementations."""

from dataclasses import dataclass, replace
from enum import Enum
from typing import ClassVar

from openhcs.constants.constants import AllComponents, VariableComponents
from openhcs.core.projected_image_output import SourceProjectedImageOutput
from openhcs.core.runtime_array_values import RuntimeArrayData
from openhcs.core.runtime_image_values import image_payload_metadata
from openhcs.core.runtime_plane_projection import RuntimePlaneAxisValueProjection


class FlatfieldCorrectionMode(Enum):
    """How an estimated illumination field is removed from an image."""

    DIVIDE = "divide"
    SUBTRACT = "subtract"


@dataclass(frozen=True)
class FittedIlluminationFieldOutput(SourceProjectedImageOutput):
    """One fitted field, owned by all independent observations, not one plane."""

    observation_axis: ClassVar[VariableComponents] = VariableComponents.SITE
    data: RuntimeArrayData
    observation_count: int

    def __post_init__(self) -> None:
        if self.observation_count < 2:
            raise ValueError("A fitted field requires multiple observations.")
        if self.data.ndim not in (2, 3):
            raise ValueError("A fitted field requires a spatial image or volume.")

    @classmethod
    def validate_observation_domain(cls, source: RuntimeArrayData) -> None:
        """Reject mislabeled metadata-backed ensembles before fitting."""
        metadata = image_payload_metadata(source)
        retained_axes = tuple(
            AllComponents.from_value(name)
            for name in metadata.retained_plane_component_values()
        )
        # Plain NumPy observations have no claimed acquisition domain. Restrict
        # annotated sources using the metadata owner's declared presence state.
        if metadata.has_values and retained_axes != (
            AllComponents.from_value(cls.observation_axis.value),
        ):
            raise ValueError(
                f"BaSiC requires independent {cls.observation_axis.name} observations "
                "with every other source component fixed."
            )

    def with_data(self, data: RuntimeArrayData) -> "FittedIlluminationFieldOutput":
        return replace(self, data=data)

    def resolve_source_context(
        self,
        source: RuntimeArrayData,
        projection: RuntimePlaneAxisValueProjection | None,
    ) -> RuntimeArrayData:
        projection = RuntimePlaneAxisValueProjection.require_complete_projection(
            projection, value_name="A fitted field"
        )
        if projection.axis_size != self.observation_count:
            raise ValueError("Fitted field observation count differs from its source.")
        if source.shape != (self.observation_count, *self.data.shape):
            raise ValueError("A fitted field must retain the source spatial grid.")
        self.validate_observation_domain(source)
        metadata = image_payload_metadata(source).collapse_leading_plane_axis()
        # Model parameters are not unit-interval input pixels. Contributor source
        # dtypes/identities remain in provenance, not on the fitted field's range.
        metadata = metadata.replace_fields(
            intensity_scale=None,
            source_dtype=None,
            unit_interval_intensity=None,
        )
        return metadata.payload_with(self.data, None)
