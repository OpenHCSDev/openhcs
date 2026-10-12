"""CellProfiler LabelImages: settings checked at import, nothing executed."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, ClassVar

from openhcs.interop.cellprofiler.module_artifact_declarations import (
    SettingsOnlyCellProfilerModule,
)
from openhcs.interop.cellprofiler.setting_names import SettingNameFamily
from openhcs.interop.cellprofiler.settings_binder import SettingToKeywordBinding

if TYPE_CHECKING:
    from openhcs.interop.cellprofiler.parser import ModuleBlock


@dataclass(frozen=True, slots=True)
class PositiveCount:
    """Parse a whole number of at least one; the error names the setting."""

    setting: str

    def __call__(self, value: str) -> int:
        try:
            count = int(value.strip())
        except ValueError:
            count = 0
        if count < 1:
            raise ValueError(
                f"{self.setting!r} must be a whole number of at least 1, "
                f"got {value!r}."
            )
        return count


@dataclass(frozen=True, slots=True)
class OneOf:
    """Parse a value that must be one of CellProfiler's choices for the setting."""

    setting: str
    choices: tuple[str, ...]

    def __call__(self, value: str) -> str:
        choice = value.strip()
        if choice not in self.choices:
            raise ValueError(
                f"{self.setting!r} must be one of {self.choices!r}, got {value!r}."
            )
        return choice


class LabelImagesModule(SettingsOnlyCellProfilerModule):
    """LabelImages is read and checked, and writes no metadata in OpenHCS.

    CellProfiler 4.2.8.1 numbers the image sets of a run 1, 2, 3, ... and this
    module turns that number into five image measurements: ``Metadata_Site``,
    ``Metadata_Row`` (letters; two letters once a plate has more than 26
    rows), ``Metadata_Column``, ``Metadata_Well`` (row letters plus the
    zero-padded column) and ``Metadata_Plate``, by dividing the image-set
    number by sites per well, then by columns or rows depending on the order.

    OpenHCS has no place a module can put metadata computed from image order.
    Source metadata comes from file names, folder names and imported tables
    (``MetadataExtractionRule``, ``ImportedMetadataTable``), and an image set's
    number is only assigned when measurements are exported. So this module
    emits no step and none of the five measurements exist because of it.

    Carried over: the four settings are parsed; a count below 1, a value that
    is not a whole number, an order other than ``Row``/``Column``, a missing
    setting or an unknown setting row fails the import.

    Not carried over: ``Metadata_Plate``, ``Metadata_Well``, ``Metadata_Row``,
    ``Metadata_Column`` and ``Metadata_Site``. A later module that names one of
    them (a file-name tag, a grouping, an export column) only finds it when the
    pipeline's Metadata module or the plate's own file names provide it.
    """

    module_name = "LabelImages"
    validated = False
    site_count_setting = SettingNameFamily("Number of image sites per well")
    column_count_setting = SettingNameFamily("Number of columns per plate")
    row_count_setting = SettingNameFamily("Number of rows per plate")
    order_setting = SettingNameFamily("Order of image data")
    setting_bindings: ClassVar[tuple[SettingToKeywordBinding, ...]] = (
        SettingToKeywordBinding(
            site_count_setting,
            "sites_per_well",
            PositiveCount(site_count_setting.canonical),
        ),
        SettingToKeywordBinding(
            column_count_setting,
            "columns_per_plate",
            PositiveCount(column_count_setting.canonical),
        ),
        SettingToKeywordBinding(
            row_count_setting,
            "rows_per_plate",
            PositiveCount(row_count_setting.canonical),
        ),
        SettingToKeywordBinding(
            order_setting,
            "order",
            OneOf(order_setting.canonical, ("Row", "Column")),
        ),
    )

    @classmethod
    def validate_pipeline_import(cls, module: ModuleBlock) -> None:
        settings = cls.checked_settings(module)
        missing = tuple(
            binding.setting_name.canonical
            for binding in cls.setting_bindings
            if binding.require_parameter_name() not in settings
        )
        if missing:
            raise ValueError(
                f"CellProfiler module {module.name}({module.module_num}) is "
                f"missing the settings {missing!r}."
            )
