"""Authored CellProfiler Analyst workspace panels and their external grammar."""

from __future__ import annotations

from openhcs.interop.cellprofiler.measurement_scope import CELLPROFILER_SCOPE_NAMES

from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import ClassVar, TYPE_CHECKING

from metaclass_registry import AutoRegisterMeta

from openhcs.core.runtime_measurements import MeasurementSubject, MeasurementScope
from openhcs.core.runtime_tabular_values import FieldSpec

from openhcs.interop.cellprofiler.database_column_dialect import (
    CellProfilerDatabaseColumnDialect,
)

from openhcs.interop.cellprofiler.parser import ModuleBlock, ModuleSetting
from openhcs.interop.cellprofiler.cellprofiler_literals import (
    cellprofiler_setting_literal,
)
from openhcs.interop.cellprofiler.setting_names import optional_setting_value
from openhcs.interop.cellprofiler.settings_binder import parse_cellprofiler_bool

if TYPE_CHECKING:
    from openhcs.processing.backends.cellprofiler.export_to_database import (
        ExportToDatabaseModule,
    )


@dataclass(frozen=True)
class CPAWorkspaceAxis(ABC, metaclass=AutoRegisterMeta):
    """One authored axis; irreducible Image/Object/Index projection on leaves."""

    __registry_key__ = "measurement_type"
    __skip_if_no_key__ = True
    measurement_type: ClassVar[str | None] = None
    object_name: str
    measurement: str
    index: str

    @classmethod
    def from_settings(
        cls, kind: str, object_name: str, measurement: str, index: str
    ) -> CPAWorkspaceAxis:
        axis_type = cls.__registry__.get(kind)
        if axis_type is None:
            raise ValueError(f"Unsupported CPA workspace measurement type {kind!r}.")
        return axis_type(object_name, measurement, index)

    def projected(self, dialect: CellProfilerDatabaseColumnDialect) -> tuple[str, str]:
        field, table = self.field_name(dialect), self.table_name(dialect)
        if not field or any(c in field for c in "\n\r\t"):
            raise ValueError("CPA workspace axis must have a single nonempty field.")
        return field, table

    @abstractmethod
    def field_name(self, dialect: CellProfilerDatabaseColumnDialect) -> str:
        """Project the authored field through the existing measurement dialect."""

    @abstractmethod
    def table_name(self, dialect: CellProfilerDatabaseColumnDialect) -> str:
        """Return the original native table role for this axis."""


class CPAImageWorkspaceAxis(CPAWorkspaceAxis):
    measurement_type = "Image"

    def field_name(self, dialect):
        return dialect.measurement_field(
            MeasurementSubject(MeasurementScope.SAMPLE, CELLPROFILER_SCOPE_NAMES[MeasurementScope.SAMPLE]),
            FieldSpec(self.measurement, None),
        ).name

    def table_name(self, dialect):
        return dialect.image_table_name()


class CPAObjectWorkspaceAxis(CPAWorkspaceAxis):
    measurement_type = "Object"

    def field_name(self, dialect):
        return dialect.measurement_field(
            MeasurementSubject(MeasurementScope.OBJECT, self.object_name),
            FieldSpec(self.measurement, None),
        ).name

    def table_name(self, dialect):
        # CP4281 workspace references Per_Object even for per-object exports.
        return dialect.combined_object_table_name()


class CPAIndexWorkspaceAxis(CPAWorkspaceAxis):
    measurement_type = "Index"

    def field_name(self, dialect):
        if self.index not in ("ImageNumber", "Group_Index"):
            raise ValueError(f"Unsupported CPA workspace index {self.index!r}.")
        return self.index

    def table_name(self, dialect):
        return dialect.image_table_name()


@dataclass(frozen=True)
class CPAWorkspacePanel(ABC, metaclass=AutoRegisterMeta):
    """One substitutable workspace tool; shared ordered external rendering."""

    __registry_key__ = "setting_name"
    __skip_if_no_key__ = True
    setting_name: ClassVar[str | None] = None
    display_name: ClassVar[str]
    x_axis_label: ClassVar[str] = "x-axis"
    x_table_label: ClassVar[str] = "table"
    x: CPAWorkspaceAxis
    y: CPAWorkspaceAxis

    @classmethod
    def bound_settings(
        cls, module: ModuleBlock, declaration: type[ExportToDatabaseModule]
    ) -> dict[str, object]:
        count_value = optional_setting_value(
            module, declaration.workspace_measurement_count_setting
        )
        count = 0 if count_value is None else int(count_value)
        names = (
            declaration.workspace_display_tool_setting,
            declaration.workspace_x_type_setting,
            declaration.workspace_x_measurement_setting,
            declaration.workspace_x_index_setting,
            declaration.workspace_y_type_setting,
            declaration.workspace_y_measurement_setting,
            declaration.workspace_y_index_setting,
        )
        values = tuple(module.get_setting_values(name.canonical) for name in names)
        for name, rows in zip(names, values, strict=True):
            declaration._require_record_count(count, name, rows)
        objects = module.get_setting_values(
            declaration.workspace_object_name_setting.canonical
        )
        declaration._require_record_count(
            count * 2, declaration.workspace_object_name_setting, objects
        )
        wants_value = optional_setting_value(
            module, declaration.wants_workspace_file_setting
        )
        wants = wants_value is not None and parse_cellprofiler_bool(wants_value)
        (
            tools,
            x_types,
            x_measurements,
            x_indices,
            y_types,
            y_measurements,
            y_indices,
        ) = values
        panels = (
            tuple(
                cls.from_settings(
                    tool,
                    CPAWorkspaceAxis.from_settings(
                        x_types[i], objects[2 * i], x_measurements[i], x_indices[i]
                    ),
                    CPAWorkspaceAxis.from_settings(
                        y_types[i], objects[2 * i + 1], y_measurements[i], y_indices[i]
                    ),
                )
                for i, tool in enumerate(tools)
            )
            if wants
            else ()
        )
        return (
            {"wants_workspace_file": True, "workspace_panels": panels} if wants else {}
        )

    @classmethod
    def setting_records(
        cls,
        declaration: type[ExportToDatabaseModule],
        *,
        wants_workspace_file: bool,
        workspace_panels: tuple[CPAWorkspacePanel, ...],
        **other_export_parameters: object,
    ) -> tuple[ModuleSetting, ...]:
        """Project workspace records from the already-bound public export call."""
        del other_export_parameters
        records = [
            ModuleSetting(
                declaration.workspace_measurement_count_setting.canonical,
                str(len(workspace_panels)),
            ),
            ModuleSetting(
                declaration.wants_workspace_file_setting.canonical,
                cellprofiler_setting_literal(wants_workspace_file),
            ),
        ]
        for panel in workspace_panels:
            values = (
                (declaration.workspace_display_tool_setting, panel.setting_name),
                (declaration.workspace_x_type_setting, panel.x.measurement_type),
                (declaration.workspace_object_name_setting, panel.x.object_name),
                (declaration.workspace_x_measurement_setting, panel.x.measurement),
                (declaration.workspace_x_index_setting, panel.x.index),
                (declaration.workspace_y_type_setting, panel.y.measurement_type),
                (declaration.workspace_object_name_setting, panel.y.object_name),
                (declaration.workspace_y_measurement_setting, panel.y.measurement),
                (declaration.workspace_y_index_setting, panel.y.index),
            )
            records.extend(
                ModuleSetting(name.canonical, value) for name, value in values
            )
        return tuple(records)

    @classmethod
    def from_settings(
        cls, tool: str, x: CPAWorkspaceAxis, y: CPAWorkspaceAxis
    ) -> CPAWorkspacePanel:
        panel_type = cls.__registry__.get(tool)
        if panel_type is None:
            raise ValueError(f"Unsupported CPA workspace display tool {tool!r}.")
        panel = panel_type(x, y)
        panel.rows(CellProfilerDatabaseColumnDialect())
        return panel

    def rows(
        self, dialect: CellProfilerDatabaseColumnDialect
    ) -> tuple[tuple[str, str], ...]:
        field, table = self.x.projected(dialect)
        return (
            (self.x_axis_label, field),
            (self.x_table_label, table),
            *self.additional_rows(dialect),
        )

    @abstractmethod
    def additional_rows(
        self, dialect: CellProfilerDatabaseColumnDialect
    ) -> tuple[tuple[str, str], ...]:
        """Irreducible tool axes beyond the common X declaration."""

    @classmethod
    def parse_workspace(
        cls, text: str
    ) -> tuple[tuple[str, tuple[tuple[str, str], ...]], ...]:
        """Read ordered panel meaning; reject unknown tools, fields and layout."""
        lines = text.splitlines()
        if len(lines) < 3 or lines[:2] != [
            "CellProfiler Analyst workflow",
            "version: 1",
        ]:
            raise ValueError("Invalid CPA workspace header.")
        if not lines[2].startswith("CP version : ") or not lines[2][13:].isdigit():
            raise ValueError("Invalid CPA workspace CellProfiler version.")
        tools = {leaf.display_name: leaf for leaf in cls.__registry__.values()}
        panels = []
        current = None
        rows = []
        for line in (*lines[3:], ""):
            if not line:
                if current is not None:
                    expected = current.external_fields()
                    if tuple(key for key, value in rows) != expected or any(
                        not value for key, value in rows
                    ):
                        raise ValueError(
                            f"Invalid CPA workspace {current.display_name} fields."
                        )
                    panels.append((current.display_name, tuple(rows)))
                    current, rows = None, []
                continue
            if current is None:
                if line not in tools:
                    raise ValueError(f"Unknown CPA workspace tool {line!r}.")
                current = tools[line]
            else:
                if not line.startswith("\t") or ": " not in line:
                    raise ValueError("Invalid CPA workspace panel field layout.")
                key, value = line[1:].split(": ", 1)
                rows.append((key, value))
        return tuple(panels)

    @classmethod
    def external_fields(cls) -> tuple[str, ...]:
        return (cls.x_axis_label, cls.x_table_label)


class CPASingleAxisWorkspacePanel(CPAWorkspacePanel, ABC):
    def additional_rows(self, dialect):
        return ()


class CPATwoAxisWorkspacePanel(CPAWorkspacePanel, ABC):
    x_table_label = "x-table"

    def additional_rows(self, dialect):
        field, table = self.y.projected(dialect)
        return (("y-axis", field), ("y-table", table))

    @classmethod
    def external_fields(cls):
        return (*super().external_fields(), "y-axis", "y-table")


class CPAScatterWorkspacePanel(CPATwoAxisWorkspacePanel):
    setting_name = "ScatterPlot"
    display_name = "Scatter"


class CPADensityWorkspacePanel(CPATwoAxisWorkspacePanel):
    setting_name = "DensityPlot"
    display_name = "Density"


class CPAHistogramWorkspacePanel(CPASingleAxisWorkspacePanel):
    setting_name = "Histogram"
    display_name = "Histogram"


class CPAPlateViewerWorkspacePanel(CPASingleAxisWorkspacePanel):
    setting_name = "PlateViewer"
    display_name = "PlateViewer"
    x_axis_label = "measurement"


class CPABoxWorkspacePanel(CPASingleAxisWorkspacePanel):
    setting_name = "BoxPlot"
    display_name = "BoxPlot"


@dataclass(frozen=True, slots=True)
class CPAWorkspaceRenderer:
    """Render the requested workspace through the export's actual table dialect."""

    dialect: CellProfilerDatabaseColumnDialect

    def render(self, panels: tuple[CPAWorkspacePanel, ...]) -> str:
        """Encode panel meaning without deciding whether an export requested it."""
        sections = tuple(
            "\n"
            + panel.display_name
            + "\n"
            + "\n".join(f"\t{key}: {value}" for key, value in panel.rows(self.dialect))
            + "\n"
            for panel in panels
        )
        return (
            "CellProfiler Analyst workflow\nversion: 1\nCP version : 4281\n"
            + "".join(sections)
        )
