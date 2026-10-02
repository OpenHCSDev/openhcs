from dataclasses import replace
from pathlib import Path

import pytest

from benchmark.cellprofiler_export_equivalence import (
    cellprofiler_database_export_equivalence,
)
from openhcs.core.equivalence.policy import RuntimeEquivalencePolicy
from openhcs.core.runtime_exports import RuntimeExportObservation
from openhcs.interop.cellprofiler.analyst_export import (
    CellProfilerDatabaseExportSettings,
    CellProfilerObjectTableMode,
)
from openhcs.interop.cellprofiler.database_column_dialect import (
    CellProfilerDatabaseColumnDialect,
)
from openhcs.interop.cellprofiler.workspace_export import (
    CPAWorkspaceAxis,
    CPAWorkspacePanel,
    CPAWorkspaceRenderer,
)
from openhcs.processing.backends.cellprofiler.export_to_database import (
    ExportToDatabaseModule,
)
from openhcs.interop.cellprofiler.parser import ModuleBlock


def settings(**kwargs):
    return replace(
        CellProfilerDatabaseExportSettings(
            sqlite_file="Database.db",
            experiment_name="Experiment",
            table_prefix="Prefix_",
            object_table_mode=CellProfilerObjectTableMode.PER_OBJECT,
            selected_objects=None,
            wants_properties_file=False,
            wants_relationship_tables=False,
        ),
        **kwargs,
    )


def axis(kind="Image", name="Intensity_MeanIntensity_DNA", index="ImageNumber"):
    return CPAWorkspaceAxis.from_settings(kind, "Nuclei", name, index)


@pytest.mark.parametrize(
    "tool,display,fields",
    [
        ("ScatterPlot", "Scatter", ("x-axis", "x-table", "y-axis", "y-table")),
        ("DensityPlot", "Density", ("x-axis", "x-table", "y-axis", "y-table")),
        ("Histogram", "Histogram", ("x-axis", "table")),
        ("BoxPlot", "BoxPlot", ("x-axis", "table")),
        ("PlateViewer", "PlateViewer", ("measurement", "table")),
    ],
)
def test_all_native_tools_preserve_axis_roles(tool, display, fields):
    panel = CPAWorkspacePanel.from_settings(tool, axis("Index"), axis("Object"))
    declaration = settings(wants_workspace_file=True, workspace_panels=(panel,))
    ((name, text),) = (
        CPAWorkspaceRenderer(CellProfilerDatabaseColumnDialect("Prefix_"))
        .render(declaration)
        .items()
    )
    assert name == "Database_Prefix.workspace"
    ((tool_name, rows),) = CPAWorkspacePanel.parse_workspace(text)
    assert tool_name == display
    assert tuple(key for key, value in rows) == fields
    assert rows[:2] == ((fields[0], "ImageNumber"), (fields[1], "Prefix_Per_Image"))
    if tool in ("ScatterPlot", "DensityPlot"):
        assert rows[2:] == (
            ("y-axis", "Nuclei_Intensity_MeanIntensity_DNA"),
            ("y-table", "Prefix_Per_Object"),
        )


def test_single_axis_tools_do_not_validate_inactive_y():
    panel = CPAWorkspacePanel.from_settings(
        "Histogram", axis(), axis(name="invalid\nfield")
    )
    assert (
        panel.rows(CellProfilerDatabaseColumnDialect())[0][1]
        == "Image_Intensity_MeanIntensity_DNA"
    )
    with pytest.raises(ValueError, match="single nonempty field"):
        CPAWorkspacePanel.from_settings(
            "ScatterPlot", axis(), axis(name="invalid\nfield")
        )


def test_disabled_workspace_emits_nothing():
    assert (
        CPAWorkspaceRenderer(CellProfilerDatabaseColumnDialect()).render(settings())
        == {}
    )


@pytest.mark.parametrize("kind,index", [("Bogus", "ImageNumber"), ("Index", "Bogus")])
def test_malformed_active_axes_reject(kind, index):
    with pytest.raises(ValueError):
        CPAWorkspacePanel.from_settings("Histogram", axis(kind, index=index), axis())


def test_workspace_module_records_round_trip_without_reordering():
    panels = (
        CPAWorkspacePanel.from_settings(
            "ScatterPlot", axis("Index", index="Group_Index"), axis("Object")
        ),
        CPAWorkspacePanel.from_settings(
            "PlateViewer", axis(), axis(name="invalid\nfield")
        ),
    )
    records = CPAWorkspacePanel.setting_records(ExportToDatabaseModule, True, panels)
    block = ModuleBlock(
        name="ExportToDatabase",
        module_num=1,
        metadata={"variable_revision_number": 28},
        enabled=True,
        setting_records=list(records),
    )
    assert CPAWorkspacePanel.bound_settings(block, ExportToDatabaseModule) == {
        "wants_workspace_file": True,
        "workspace_panels": panels,
    }
    with pytest.raises(ValueError):
        CPAWorkspacePanel.bound_settings(
            replace(block, setting_records=list(records[:-1])), ExportToDatabaseModule
        )


@pytest.mark.parametrize(
    "replacement",
    [
        "Unknown",
        "Scatter\n\tx-axis: X",
        "Scatter\n\tx-axis: X\n\tx-axis: Y\n\ty-axis: Z\n\ty-table: T",
    ],
)
def test_workspace_reader_rejects_unknown_missing_duplicate_fields(replacement):
    with pytest.raises(ValueError):
        CPAWorkspacePanel.parse_workspace(
            "CellProfiler Analyst workflow\nversion: 1\nCP version : 4281\n\n"
            + replacement
            + "\n"
        )


def test_workspace_comparison_covers_order_values_and_missing_files(tmp_path):
    native = (
        Path(__file__).parents[1]
        / "fixtures/cellprofiler/quality_control_4281.workspace"
    ).read_text()
    reference = tmp_path / "reference"
    reference.mkdir()
    candidate = tmp_path / "candidate"
    candidate.mkdir()
    (reference / "QC.workspace").write_text(native)
    (candidate / "QC.workspace").write_text(native)
    policy = RuntimeEquivalencePolicy()
    compare = lambda: cellprofiler_database_export_equivalence(
        reference,
        RuntimeExportObservation.from_output_roots((candidate,)),
        policy=policy,
    )
    assert compare().is_equivalent
    (candidate / "QC.workspace").write_text(
        native.replace("ImageNumber", "Group_Index", 1)
    )
    assert not compare().is_equivalent
    (candidate / "QC.workspace").unlink()
    assert not compare().is_equivalent


def test_native_quality_control_fixture_contains_twelve_ordered_panels():
    native = (
        Path(__file__).parents[1]
        / "fixtures/cellprofiler/quality_control_4281.workspace"
    ).read_text()
    panels = CPAWorkspacePanel.parse_workspace(native)
    assert (
        tuple(tool for tool, rows in panels) == ("Scatter",) * 10 + ("Histogram",) * 2
    )
    assert panels[0][1][2][1] == "Image_ImageQuality_PowerLogLogSlope_OrigER"
    assert panels[-1][1][0][1] == "Image_ImageQuality_ThresholdOtsu_OrigPh_golgi_3FW"


def test_workspace_panels_survive_source_transport():
    import openhcs.serialization.pycodify_formatters
    from pycodify import Assignment, generate_python_source

    panels = (
        CPAWorkspacePanel.from_settings("ScatterPlot", axis("Index"), axis("Object")),
    )
    source = generate_python_source(Assignment("panels", panels), clean_mode=True)
    namespace = {}
    exec(source, namespace)
    assert namespace["panels"] == panels


def test_workspace_dialect_must_match_its_export_request():
    panel = CPAWorkspacePanel.from_settings("Histogram", axis(), axis())
    with pytest.raises(ValueError, match="table prefix"):
        CPAWorkspaceRenderer(CellProfilerDatabaseColumnDialect("Other_")).render(
            settings(wants_workspace_file=True, workspace_panels=(panel,))
        )


def test_workspace_filename_preserves_native_relative_directory_and_single_suffix():
    panel = CPAWorkspacePanel.from_settings("Histogram", axis(), axis())
    declaration = settings(
        sqlite_file="nested/Database.sqlite",
        table_prefix="Prefix__",
        wants_workspace_file=True,
        workspace_panels=(panel,),
    )
    assert tuple(
        CPAWorkspaceRenderer(CellProfilerDatabaseColumnDialect("Prefix__")).render(
            declaration
        )
    ) == ("nested/Database_Prefix_.workspace",)


def test_workspace_reader_rejects_malformed_version_and_reordered_fields():
    native = (
        Path(__file__).parents[1]
        / "fixtures/cellprofiler/quality_control_4281.workspace"
    ).read_text()
    for malformed in (
        native.replace("version: 1", "version: 2"),
        native.replace("CP version : 4281", "CP version : unknown"),
        native.replace(
            "\tx-axis: ImageNumber\n\tx-table: BBBC022QC_Per_Image",
            "\tx-table: BBBC022QC_Per_Image\n\tx-axis: ImageNumber",
            1,
        ),
    ):
        with pytest.raises(ValueError):
            CPAWorkspacePanel.parse_workspace(malformed)
