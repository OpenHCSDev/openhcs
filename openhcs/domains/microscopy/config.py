"""Microscopy configuration sections: plate result consolidation and analysis.

Listed in ``Microscopy.config_modules``: the kernel config adds every
:class:`GlobalConfigSection` declared here as a ``GlobalPipelineConfig`` field.
"""

from collections.abc import Callable
from dataclasses import dataclass
from enum import Enum
from typing import Annotated, Optional

from objectstate import abbreviation
from python_introspect import AnnotatedDataclassValidationMixin, Enableable
from zmqruntime.config import PositiveFloat

from openhcs.core.config_sections import GlobalConfigSection


class NormalizationMethod(Enum):
    """Control-normalization declarations with member-owned calculations."""

    FOLD_CHANGE = (
        "fold_change",
        lambda value, control_mean, _control_std: (
            value / control_mean if control_mean else None
        ),
    )
    Z_SCORE = (
        "z_score",
        lambda value, control_mean, control_std: (
            (value - control_mean) / control_std if control_std else None
        ),
    )
    PERCENT_CONTROL = (
        "percent_control",
        lambda value, control_mean, _control_std: (
            (value / control_mean) * 100 if control_mean else None
        ),
    )

    def __new__(
        cls,
        serialized_value: str,
        operation: Callable[[float, float, float], float | None],
    ) -> "NormalizationMethod":
        member = object.__new__(cls)
        member._value_ = serialized_value
        member._operation = operation
        return member

    def normalize(
        self,
        value: float,
        *,
        control_mean: float,
        control_std: float,
    ) -> float | None:
        """Normalize one value against its control reference."""
        return self._operation(value, control_mean, control_std)


@abbreviation("analysis")
@dataclass(frozen=True)
class AnalysisConsolidationConfig(
    GlobalConfigSection, AnnotatedDataclassValidationMixin, Enableable
):
    """Combine materialized per-well analysis tables after plate execution."""

    enabled: Annotated[bool, abbreviation("")] = True
    """Run table discovery and summary generation after a plate finishes."""

    metaxpress_style: Annotated[bool, abbreviation("mx_style")] = True
    """Write MetaXpress-compatible metadata headers and grouped column ordering.

    When false, the consolidated result is a plain CSV with ``Well`` first and
    remaining columns sorted by name.
    """

    file_extensions: Annotated[tuple[str, ...], abbreviation("exts")] = (".csv",)
    """Exact filename suffixes considered when discovering analysis tables."""

    exclude_patterns: Annotated[tuple[str, ...], abbreviation("exclude")] = (
        r".*consolidated.*",
        r".*metaxpress.*",
        r".*summary.*",
    )
    """Regular expressions matched against filenames after extension filtering.

    Matching files are skipped; the defaults prevent prior summaries from being
    recursively consolidated into a new summary.
    """

    output_filename: Annotated[str, abbreviation("out_file")] = (
        "metaxpress_style_summary.csv"
    )
    """Filename for the summary produced from one plate's included analysis tables."""

    global_summary_filename: Annotated[str, abbreviation("global_sum")] = (
        "global_metaxpress_summary.csv"
    )
    """Filename for the optional summary that combines completed plate summaries."""


@abbreviation("plate")
@dataclass(frozen=True)
class PlateMetadataConfig(GlobalConfigSection, AnnotatedDataclassValidationMixin):
    """Metadata written into MetaXpress-compatible consolidated result headers."""

    barcode: Annotated[Optional[str], abbreviation("barcode")] = None
    """Barcode written to the summary header; ``None`` derives one from the results directory."""

    plate_name: Annotated[Optional[str], abbreviation("name")] = None
    """Plate name written to the summary header; ``None`` uses the results directory name."""

    plate_id: Annotated[Optional[str], abbreviation("id")] = None
    """Plate identifier written to the summary header; ``None`` derives a numeric value from the results path for the current process."""

    description: Annotated[Optional[str], abbreviation("description")] = None
    """Experiment description written to the summary header; ``None`` reports the number of analysed wells."""

    acquisition_user: Annotated[str, abbreviation("user")] = "OpenHCS"
    """Acquisition-user text written to the MetaXpress-compatible header."""

    z_step: Annotated[PositiveFloat, abbreviation("z_step")] = 1.0
    """Positive Z-plane spacing recorded in the MetaXpress-compatible header."""


@dataclass(frozen=True)
class ExperimentalAnalysisConfig(AnnotatedDataclassValidationMixin):
    """Standalone configuration for the experimental-analysis engine."""

    config_file_name: Annotated[str, abbreviation("config")] = "config.xlsx"
    """Name of the experimental configuration Excel file."""

    results_file_name: Annotated[str, abbreviation("results")] = (
        "metaxpress_style_summary.csv"
    )
    """Name of the consolidated microscope results file."""

    compiled_results_file_name: Annotated[str, abbreviation("output")] = (
        "compiled_results_normalized.xlsx"
    )
    """Name of the normalized analysis workbook written by the directory workflow."""

    raw_results_file_name: Annotated[str, abbreviation("raw_output")] = (
        "compiled_results_raw.xlsx"
    )
    """Name of the non-normalized analysis workbook written when raw export is enabled."""

    heatmap_file_name: Annotated[str, abbreviation("heatmap")] = "heatmaps.xlsx"
    """Name of the heatmap workbook written when heatmap export is enabled."""

    design_sheet_name: Annotated[str, abbreviation("design")] = "drug_curve_map"
    """Name of the sheet containing experimental design."""

    plate_groups_sheet_name: Annotated[str, abbreviation("groups")] = "plate_groups"
    """Name of the sheet containing plate group mappings."""

    normalization_method: Annotated[NormalizationMethod, abbreviation("norm")] = (
        NormalizationMethod.FOLD_CHANGE
    )
    """Replicate-local control transformation: value/control mean, control
    z-score, or percentage of control mean. A zero required denominator produces
    a missing normalized value rather than an infinite result."""

    export_raw_results: Annotated[bool, abbreviation("raw")] = True
    """Whether to export raw (non-normalized) results."""

    export_heatmaps: Annotated[bool, abbreviation("heatmaps")] = True
    """Whether to generate heatmap visualizations."""
