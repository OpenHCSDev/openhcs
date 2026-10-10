"""Executable CellProfiler ExportToSpreadsheet boundary tests."""

from __future__ import annotations

import csv
import inspect
import io
import math
from collections import OrderedDict

import pytest

from polystore.filemanager import FileManager
from polystore.memory import MemoryStorageBackend

from openhcs.core.artifacts import (
    ObjectLabelsArtifactType,
    ArtifactInputPlan,
    ArtifactOutputPlan,
    ArtifactSpec,
    ArtifactSpecCollection,
    ImageArtifactType,
    MeasurementsArtifactType,
    SpatialGridArtifactType,
    RelationshipsArtifactType,
    SpecialArtifactType,
)
from openhcs.core.callable_contract import CallableContract, FunctionStepExecutionScope
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.function_patterns import FunctionInvocationKey
from openhcs.core.invocation_artifacts import ArtifactDeclarationStepContext
from openhcs.core.pipeline.artifact_planning import artifact_producers_for_outputs
from openhcs.core.runtime_artifact_values import RuntimeValue
from openhcs.core.measurement_row_materialization import (
    MeasurementSparseColumnarRows,
    MEASUREMENT_SPARSE_CELL,
)
from openhcs.core.runtime_tabular_values import (
    FieldSpec,
)
from openhcs.core.runtime_measurements import (
    MeasurementScope,
    MeasurementSubject,
)
from openhcs.core.runtime_relationships import (
    DirectedObjectRelationshipPayload,
    ObjectRelationshipDeclaration,
)
from openhcs.core.runtime_stores import (
    RuntimeArtifactBatch,
    RuntimeArtifactLocation,
    StoredRuntimeValue,
)
from openhcs.core.runtime_measurements import (
    MeasurementTable,
)
from openhcs.core.runtime_tabular_values import ColumnarRows
from openhcs.core.runtime_relationships import (
    ObjectRelationship,
)
from openhcs.core.source_image_provenance import (
    SourceImageProvenancePlanes,
    SourceImageProvenance,
    RuntimeSourceImageProvenancePlane,
    SourceImageProvenanceContributor,
    SourceImageIdentity,
)
from openhcs.core.source_matching import SourceImageSetIdentityPolicy
from openhcs.core.source_bindings import (
    ComponentSelector,
    NamedSourceBinding,
    SourceBindingsConfig,
)
from openhcs.core.source_metadata import DECLARED_SOURCE_METADATA_FIELD
from openhcs.interop.cellprofiler.module_declarations import (
    CellProfilerModule,
)
from openhcs.interop.cellprofiler.module_settings import (
    ModuleSettingCoverageStatus,
)
from openhcs.interop.cellprofiler.worm_measurements import (
    WormControlPointAxis,
    WormControlPointMeasurementField,
)
from openhcs.interop.cellprofiler.parser import ModuleBlock, ModuleSetting
from openhcs.interop.cellprofiler.settings_binder import SettingsBinder
from openhcs.processing.backends.cellprofiler.spreadsheet_export import (
    ExportToSpreadsheetModule,
    SpreadsheetColumnSelection,
    SpreadsheetDelimiter,
    SpreadsheetFileSelection,
    SpreadsheetNanRepresentation,
    export_to_spreadsheet,
    render_spreadsheet_bundle,
)
from openhcs.processing.backends.cellprofiler.intensity import (
    MeasureObjectIntensityModule,
)
from openhcs.processing.backends.cellprofiler.crop import CropModule
from openhcs.processing.backends.cellprofiler.tracking import TrackObjectsModule
from openhcs.processing.materialization import (
    FileBundleOptions,
    MaterializationSpec,
    WriteMode,
    materialize,
    materialization_outputs,
)
from openhcs.core.axes import Axis
from openhcs.domains.microscopy.axes import Microscopy

def test_export_to_spreadsheet_declares_exact_plate_callable_abi() -> None:
    contract = CallableContract.from_callable(export_to_spreadsheet)
    parameter = inspect.signature(export_to_spreadsheet).parameters["artifact_batch"]
    module_type = CellProfilerModule.require_module("ExportToSpreadsheet")

    assert ExportToSpreadsheetModule.emits_function_step()
    assert not ExportToSpreadsheetModule.uses_cellprofiler_runtime_adapter()
    assert module_type is ExportToSpreadsheetModule
    assert module_type.require_callable() is export_to_spreadsheet
    assert export_to_spreadsheet.__module__ == module_type.__module__
    assert module_type.__module__ == (
        "openhcs.processing.backends.cellprofiler.spreadsheet_export"
    )
    assert contract.execution_scope is FunctionStepExecutionScope.PLATE
    assert contract.processing_contract is None
    assert contract.runtime_adapter is None
    assert contract.runtime_bound_parameter_types == (RuntimeArtifactBatch,)
    assert parameter.kind is inspect.Parameter.KEYWORD_ONLY
    assert parameter.default is inspect.Parameter.empty


def test_export_to_spreadsheet_contract_selects_ordered_tables_and_declares_bundle() -> (
    None
):
    available = ArtifactSpecCollection(
        (
            ArtifactSpec.output("measurements_a", MeasurementsArtifactType),
            ArtifactSpec.output("pixels", ImageArtifactType),
            ArtifactSpec.output("relationships", RelationshipsArtifactType),
            ArtifactSpec.output("measurements_b", MeasurementsArtifactType),
        )
    )
    contract = ExportToSpreadsheetModule.callable_contract(
        module=ModuleBlock(name="ExportToSpreadsheet", module_num=99),
        invocation_key=FunctionInvocationKey(
            function_name="export_to_spreadsheet",
            group_key="default",
            position=0,
        ),
        step_context=ArtifactDeclarationStepContext(
            step_index=4,
            available_artifacts=available,
            main_flow_artifacts=ArtifactSpecCollection(()),
            available_artifact_producers=artifact_producers_for_outputs(
                tuple(
                    spec for spec in available if spec.plan_type is ArtifactOutputPlan
                ),
                groups=(None,),
                invocation_keys=(
                    FunctionInvocationKey("fixture_producer", "default", 0),
                ),
            ),
        ),
    )

    runtime_inputs = contract.artifact_inputs
    declared_outputs = contract.artifact_outputs

    assert tuple(spec.name for spec in runtime_inputs) == (
        "measurements_a",
        "relationships",
        "measurements_b",
    )
    assert all(spec.plan_type is ArtifactInputPlan for spec in runtime_inputs)
    assert len(declared_outputs) == 1
    assert declared_outputs[0].name == "ExportToSpreadsheet_5_files"
    assert declared_outputs[0].artifact_type is SpecialArtifactType
    assert isinstance(declared_outputs[0].materialization, MaterializationSpec)
    assert declared_outputs[0].materialization.outputs == (FileBundleOptions(),)
    assert tuple(
        relation.source for relation in declared_outputs[0].relations
    ) == tuple(spec.ref() for spec in runtime_inputs)


def test_export_to_spreadsheet_binds_scalars_and_repeated_file_rows() -> None:
    module = _module(
        (
            ("Select the column delimiter", 'Comma (",")'),
            ("Add image metadata columns to your object data file?", "Yes"),
            ("Add image file and folder names to your object data file?", "No"),
            ("Select measurements to export", "Yes"),
            (
                "Calculate the per-image mean values for object measurements?",
                "Yes",
            ),
            (
                "Calculate the per-image median values for object measurements?",
                "No",
            ),
            (
                "Calculate the per-image standard deviation values for object measurements?",
                "No",
            ),
            ("Output file location", r"Default Output Folder sub-folder|\g<Run>"),
            ("Create a GenePattern GCT file?", "No"),
            ("Select source of sample row name", "Metadata"),
            ("Select the image to use as the identifier", "None"),
            ("Select the metadata to use as the identifier", "None"),
            ("Export all measurement types?", "No"),
            ("Press button to select measurements", "Image|Count,Cells|Area"),
            ("Representation of Nan/Inf", "Null"),
            ("Add a prefix to file names?", "Yes"),
            ("Filename prefix", "Plate_"),
            ("Overwrite existing files without warning?", "Yes"),
            ("Data to export", "Image"),
            (
                "Combine these object measurements with those of the previous object?",
                "No",
            ),
            ("File name", "image-data.csv"),
            ("Use the object name for the file name?", "No"),
            ("Data to export", "Cells"),
            (
                "Combine these object measurements with those of the previous object?",
                "No",
            ),
            ("File name", "DATA.csv"),
            ("Use the object name for the file name?", "Yes"),
            ("Data to export", "Cytoplasm"),
            (
                "Combine these object measurements with those of the previous object?",
                "Yes",
            ),
            ("File name", "unused.csv"),
            ("Use the object name for the file name?", "Yes"),
        )
    )

    bound = ExportToSpreadsheetModule.bind_settings(
        module,
        binder=SettingsBinder(),
    )

    assert bound.kwargs["delimiter"] is SpreadsheetDelimiter.COMMA
    assert bound.kwargs["selected_columns"] == (
        SpreadsheetColumnSelection("Image", "Count"),
        SpreadsheetColumnSelection("Cells", "Area"),
    )
    assert bound.kwargs["nan_representation"] is SpreadsheetNanRepresentation.NULL
    assert bound.kwargs["output_directory"] == "{Run}"
    assert bound.kwargs["file_selections"] == (
        SpreadsheetFileSelection(("Image",), "image-data.csv"),
        SpreadsheetFileSelection(("Cells", "Cytoplasm"), "Cells.csv"),
    )
    assert not bound.unmapped_kwargs
    assert {record.status for record in bound.setting_coverage} <= {
        ModuleSettingCoverageStatus.BOUND,
        ModuleSettingCoverageStatus.IGNORED,
    }


def test_export_to_spreadsheet_overwrite_setting_is_contract_owned() -> None:
    module = _module((("Overwrite existing files without warning?", "No"),))

    bound = ExportToSpreadsheetModule.bind_settings(
        module,
        binder=SettingsBinder(),
    )
    contract = ExportToSpreadsheetModule.callable_contract(
        module=module,
        invocation_key=FunctionInvocationKey(
            function_name="export_to_spreadsheet",
            group_key="default",
            position=0,
        ),
        step_context=ArtifactDeclarationStepContext(
            step_index=0,
            available_artifacts=ArtifactSpecCollection(()),
            main_flow_artifacts=ArtifactSpecCollection(()),
        ),
    )
    output = contract.artifact_outputs[0]

    assert bound.kwargs["overwrite_existing_files_without_warning"] is False
    assert not bound.unmapped_kwargs
    assert output.materialization.write_mode is WriteMode.ERROR


def test_export_to_spreadsheet_ignores_disabled_excel_size_limit() -> None:
    bound = ExportToSpreadsheetModule.bind_settings(
        _module((("Limit output to a size that is allowed in Excel", "No"),)),
        binder=SettingsBinder(),
    )

    assert not bound.unmapped_kwargs
    assert bound.kwargs == {"file_selections": ()}


def test_export_to_spreadsheet_rejects_enabled_excel_size_limit() -> None:
    with pytest.raises(ValueError, match="Excel row and column truncation"):
        ExportToSpreadsheetModule.bind_settings(
            _module((("Limit output to a size that is allowed in Excel", "Yes"),)),
            binder=SettingsBinder(),
        )


def test_export_to_spreadsheet_renders_only_declared_batch_records() -> None:
    measurements_a = _measurement_record(
        "measurements_a",
        axis_id="A01",
        subject=MeasurementSubject(MeasurementScope.SAMPLE, "Image"),
        rows=(
            {
                "slice_index": 0,
                "feature_name": "Count",
                "value": 2.0,
            },
            {
                "slice_index": 0,
                "feature_name": "BadValue",
                "value": float("nan"),
            },
        ),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            component_metadata=(
                {
                    "site": "1",
                    "source_alias": "OrigColor",
                    DECLARED_SOURCE_METADATA_FIELD: {
                        "Run": "Run1",
                        "FrameNumber": "0",
                    },
                },
            )
        ),
    )
    cells = _measurement_record(
        "cells",
        axis_id="A01",
        subject=MeasurementSubject(MeasurementScope.OBJECT, "Cells", "object_number"),
        rows=(
            {"slice_index": 0, "object_number": 1, "Area": 2.0, "Ignored": 9},
            {"slice_index": 0, "object_number": 2, "Area": 4.0, "Ignored": 8},
        ),
    )
    relationships = _relationship_record("relationships", axis_id="A01")
    undeclared = _measurement_record(
        "undeclared",
        axis_id="A01",
        subject=MeasurementSubject(MeasurementScope.SAMPLE, "Image"),
        rows=({"slice_index": 0, "Leaked": 999},),
    )
    batch = RuntimeArtifactBatch(
        input_specs=(
            ArtifactSpec.input("measurements_a", MeasurementsArtifactType),
            ArtifactSpec.input("cells", MeasurementsArtifactType),
            ArtifactSpec.input("relationships", RelationshipsArtifactType),
        ),
        records_by_axis={
            "A01": (undeclared, relationships, cells, measurements_a),
        },
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    bundle = render_spreadsheet_bundle(
        select_measurements=True,
        selected_columns=(
            SpreadsheetColumnSelection("Image", "Count"),
            SpreadsheetColumnSelection("Image", "BadValue"),
            SpreadsheetColumnSelection("Image", "Metadata_FrameNumber"),
            SpreadsheetColumnSelection("Cells", "Area"),
        ),
        calculate_aggregate_means=True,
        output_directory="{Run}",
        export_all_measurement_types=False,
        file_selections=(
            SpreadsheetFileSelection(("Image",), "Image.csv"),
            SpreadsheetFileSelection(("Cells",), "Cells.csv"),
            SpreadsheetFileSelection(
                ("Object relationships",),
                "Relationships.csv",
            ),
        ),
        nan_representation=SpreadsheetNanRepresentation.NULL,
        add_filename_prefix=False,
        artifact_batch=batch,
    )

    assert type(bundle) is dict
    assert tuple(bundle) == (
        "Run1/Image.csv",
        "Run1/Cells.csv",
        "Run1/Relationships.csv",
    )
    image_rows = tuple(csv.DictReader(io.StringIO(bundle["Run1/Image.csv"])))
    cell_rows = tuple(csv.DictReader(io.StringIO(bundle["Run1/Cells.csv"])))
    relationship_rows = tuple(
        csv.DictReader(io.StringIO(bundle["Run1/Relationships.csv"]))
    )
    assert image_rows == (
        {
            "image_number": "1",
            "Count": "2.0",
            "BadValue": "",
            "Metadata_FrameNumber": "0",
            "Mean_Cells_Area": "3.0",
        },
    )
    assert cell_rows == (
        {"image_number": "1", "object_number": "1", "Area": "2.0"},
        {"image_number": "1", "object_number": "2", "Area": "4.0"},
    )
    assert relationship_rows[0]["relationship_type"] == "related"
    assert relationship_rows[0]["source_role"] == "parent"
    assert relationship_rows[0]["target_role"] == "child"
    assert "Leaked" not in bundle["Run1/Image.csv"]
    assert "Ignored" not in bundle["Run1/Cells.csv"]


@pytest.mark.parametrize("add_metadata", (False, True))
@pytest.mark.parametrize("add_files", (False, True))
@pytest.mark.parametrize("axisless", (False, True))
def test_spreadsheet_projects_source_identity_without_upstream_image_features(
    add_metadata: bool, add_files: bool, axisless: bool,
) -> None:
    provenance = SourceImageProvenancePlanes((
        RuntimeSourceImageProvenancePlane(
            SourceImageIdentity('/acquisition/body.tif', {
                'well': 'A01', 'site': '2', 'channel': '3', 'z_index': '4',
                'timepoint': '5', DECLARED_SOURCE_METADATA_FIELD: {'Treatment': 'control'},
            }),
            source_image_name='Body',
        ),
    ))
    cells = _measurement_record(
        'cells', axis_id='A01',
        subject=MeasurementSubject(MeasurementScope.OBJECT, 'Cells', 'object_number'),
        rows=({**({} if axisless else {'slice_index': 0}), 'object_number': 7, 'Area': 12.0},),
        source_image_provenance_planes=provenance,
    )
    bundle = render_spreadsheet_bundle(
        artifact_batch=RuntimeArtifactBatch(
            input_specs=(ArtifactSpec.input('cells', MeasurementsArtifactType),),
            records_by_axis={'A01': (cells,)},
            source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
        ),
        add_image_metadata=add_metadata, add_image_file_names=add_files,
        add_filename_prefix=False,
    )
    image, = csv.DictReader(io.StringIO(bundle['Image.csv']))
    cell, = csv.DictReader(io.StringIO(bundle['Cells.csv']))
    assert image['Metadata_Treatment'] == 'control'
    assert ('Metadata_site' in image) is add_metadata
    assert ('FileName_Body' in image) is add_files
    if add_metadata:
        assert image['Metadata_well'] == 'A01'
        assert image['Metadata_site'] == '2'
        assert image['Metadata_z_index'] == '4'
        assert image['Metadata_timepoint'] == '5'
    if add_files:
        assert image['FileName_Body'] == 'body.tif'
        assert image['PathName_Body'] == '/acquisition'
    assert cell['object_number'] == '7'
    assert cell['Area'] == '12.0'
    assert ('Metadata_site' in cell) is add_metadata
    assert ('Image_FileName_Body' in cell) is add_files
    if add_files:
        assert cell['Image_FileName_Body'] == 'body.tif'
        assert cell['Image_PathName_Body'] == '/acquisition'


@pytest.mark.parametrize('names', (('Body', 'Nuclear'), ('Nuclear', 'Body')))
def test_spreadsheet_preserves_independent_contributor_filenames(names: tuple[str, ...]) -> None:
    provenance = SourceImageProvenancePlanes((
        RuntimeSourceImageProvenancePlane(
            SourceImageIdentity(component_metadata={'well': 'A01', 'site': '2'}),
            contributors=tuple(
                SourceImageProvenanceContributor(
                    SourceImageIdentity(f'/acquisition/{name}.tif', {'well': 'A01', 'site': '2'}),
                    source_image_name=name,
                )
                for name in names
            ),
        ),
    ))
    record = _measurement_record(
        'cells', axis_id='A01',
        subject=MeasurementSubject(MeasurementScope.OBJECT, 'Cells', 'object_number'),
        rows=({'slice_index': 0, 'object_number': 1, 'Area': 12.0},),
        source_image_provenance_planes=provenance,
    )
    bundle = render_spreadsheet_bundle(
        artifact_batch=RuntimeArtifactBatch(
            input_specs=(ArtifactSpec.input('cells', MeasurementsArtifactType),),
            records_by_axis={'A01': (record,)},
            source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
        ),
        add_image_metadata=True, add_image_file_names=True, add_filename_prefix=False,
    )
    row, = csv.DictReader(io.StringIO(bundle['Cells.csv']))
    for name in names:
        assert row[f'Image_FileName_{name}'] == f'{name}.tif'
        assert row[f'Image_PathName_{name}'] == '/acquisition'
    assert 'Metadata_channel' not in row
    assert 'Metadata_z_index' not in row


def test_requested_source_columns_preserve_original_extraction_path_template() -> None:
    image = _measurement_record(
        'image', axis_id='A01',
        subject=MeasurementSubject(MeasurementScope.SAMPLE, 'Image'),
        rows=({'slice_index': 0, 'Count_Cells': 1},),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            component_metadata=({'site': '1', DECLARED_SOURCE_METADATA_FIELD: {'Run': 'run1'}},),
        ),
    )
    cells = _measurement_record(
        'cells', axis_id='A01',
        subject=MeasurementSubject(MeasurementScope.OBJECT, 'Cells', 'object_number'),
        rows=({'slice_index': 0, 'object_number': 1, 'Area': 12.0},),
    )
    bundle = render_spreadsheet_bundle(
        artifact_batch=RuntimeArtifactBatch(
            input_specs=tuple(ArtifactSpec.input(record.key.name, MeasurementsArtifactType) for record in (image, cells)),
            records_by_axis={'A01': (image, cells)},
            source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
        ),
        add_image_metadata=True, add_image_file_names=True,
        output_directory='{Run}', add_filename_prefix=False,
    )
    assert set(bundle) == {'run1/Image.csv', 'run1/Cells.csv'}
    row, = csv.DictReader(io.StringIO(bundle['run1/Cells.csv']))
    assert row['Metadata_Run'] == 'run1'
    assert row['Metadata_site'] == '1'


def test_spreadsheet_rejects_existing_filename_conflicting_with_provenance() -> None:
    record = _measurement_record(
        'image', axis_id='A01',
        subject=MeasurementSubject(MeasurementScope.SAMPLE, 'Image'),
        rows=({'slice_index': 0, 'FileName_Body': 'other.tif'},),
        source_image_provenance_planes=SourceImageProvenancePlanes((
            RuntimeSourceImageProvenancePlane(
                SourceImageIdentity('/acquisition/body.tif', {'site': '1'}),
                source_image_name='Body',
            ),
        )),
    )
    with pytest.raises(ValueError, match='Conflicting sparse measurement values'):
        render_spreadsheet_bundle(
            artifact_batch=RuntimeArtifactBatch(
                input_specs=(ArtifactSpec.input('image', MeasurementsArtifactType),),
                records_by_axis={'A01': (record,)},
                source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
            ),
            add_image_file_names=True,
        )


def test_export_to_spreadsheet_bundle_uses_generic_file_materialization() -> None:
    batch = RuntimeArtifactBatch(
        input_specs=(ArtifactSpec.input("measurements", MeasurementsArtifactType),),
        records_by_axis={
            axis: (
                _measurement_record(
                    "measurements",
                    axis_id=axis,
                    subject=MeasurementSubject(MeasurementScope.SAMPLE, "Image"),
                    rows=({"slice_index": 0, "Count": count},),
                ),
            )
            for axis, count in (("A01", 3), ("A02", 7))
        },
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )
    filemanager = FileManager({"memory": MemoryStorageBackend()})
    context = ProcessingContext(filemanager=filemanager)
    with context.runtime_step_scope():
        bundle = export_to_spreadsheet(
            add_filename_prefix=False,
            artifact_batch=batch,
            context=context,
        )
        from openhcs.processing.materialization.core import ColumnarCsvOutput
        assert all(isinstance(output, ColumnarCsvOutput) for output in bundle.values())
        outputs = materialization_outputs(
            MaterializationSpec(FileBundleOptions()),
            data=bundle,
            path="/analysis/ExportToSpreadsheet_1_files.pkl",
            filemanager=filemanager,
            context=context,
        )
        assert len(outputs) == 1
        assert outputs[0].path == "/analysis/Image.csv"
        assert outputs[0].sample_numbers_by_axis == {"A01": (1,), "A02": (2,)}
        primary_path = materialize(
            MaterializationSpec(FileBundleOptions()),
            data=bundle,
            path="/analysis/ExportToSpreadsheet_1_files.pkl",
            filemanager=filemanager,
            backends=("memory",),
            context=context,
        )
    assert context.runtime_step_outputs is None
    assert primary_path == "/analysis/Image.csv"
    assert filemanager.load(primary_path, "memory") == b"image_number,Count\n1,3\n2,7\n"


def test_columnar_aggregates_preserve_missing_cells_and_exclude_non_numeric_values():
    image = _measurement_record(
        "image",
        axis_id="A01",
        subject=MeasurementSubject(MeasurementScope.SAMPLE, "Image"),
        rows=({"slice_index": 0, "Count": 3},),
    )
    object_rows = (
        {
            "slice_index": 0,
            "object_number": 2,
            "Numeric": 2.0,
            "WithNone": None,
            "WithNaN": float("nan"),
            "Boolean": True,
        },
        {
            "slice_index": 0,
            "object_number": 17,
            "Numeric": 4.0,
            "WithNone": 4.0,
            "WithNaN": 4.0,
            "Boolean": False,
            "Sparse": 3.0,
        },
        {
            "slice_index": 0,
            "object_number": 32,
            "Numeric": 6.0,
            "WithNone": 6.0,
            "WithNaN": 6.0,
            "Boolean": True,
            "Sparse": 5.0,
        },
    )
    objects = _measurement_record(
        "objects",
        axis_id="A01",
        subject=MeasurementSubject(MeasurementScope.OBJECT, "Cells", "object_number"),
        rows=MeasurementSparseColumnarRows.from_rows(
            object_rows,
            fields=tuple(
                (
                    FieldSpec(name, int)
                    if name in ("slice_index", "object_number")
                    else FieldSpec(name, required=False)
                )
                for name in dict.fromkeys(name for row in object_rows for name in row)
            ),
        ),
    )
    batch = RuntimeArtifactBatch(
        input_specs=(
            ArtifactSpec.input("image", MeasurementsArtifactType),
            ArtifactSpec.input("objects", MeasurementsArtifactType),
        ),
        records_by_axis={"A01": (image, objects)},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )
    bundle = render_spreadsheet_bundle(
        artifact_batch=batch,
        calculate_aggregate_means=True,
        export_all_measurement_types=False,
        file_selections=(
            SpreadsheetFileSelection(("Image",), "Image.csv"),
            SpreadsheetFileSelection(("Cells",), "Cells.csv"),
        ),
        add_filename_prefix=False,
    )
    row = next(csv.DictReader(io.StringIO(bundle["Image.csv"])))
    assert row["Mean_Cells_Numeric"] == "4.0"
    assert row["Mean_Cells_Sparse"] == "4.0"
    assert row["Mean_Cells_WithNaN"] == "NaN"
    assert not any(
        name in row for name in ("Mean_Cells_WithNone", "Mean_Cells_Boolean")
    )
    object_rows = tuple(csv.DictReader(io.StringIO(bundle["Cells.csv"])))
    assert tuple(row["object_number"] for row in object_rows) == ("2", "17", "32")
    assert object_rows[0]["Sparse"] == ""


def test_export_to_spreadsheet_rejects_append_order_slice_synthesis() -> None:
    records = tuple(
        _measurement_record(
            "align_measurements",
            axis_id="A01",
            subject=MeasurementSubject(MeasurementScope.SAMPLE, "Image"),
            rows=(
                {
                    "slice_index": 0,
                    "source_image_name": "Stain2",
                    "Align_Xshift": shift,
                },
            ),
        )
        for shift in (-1.0, -2.0)
    )
    batch = RuntimeArtifactBatch(
        input_specs=(
            ArtifactSpec.input("align_measurements", MeasurementsArtifactType),
        ),
        records_by_axis={"A01": records},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    with pytest.raises(ValueError, match="Conflicting sparse measurement values"):
        render_spreadsheet_bundle(
            add_filename_prefix=False,
            artifact_batch=batch,
        )


def test_export_to_spreadsheet_projects_site_group_scope_without_relabeling_stack() -> (
    None
):
    records = tuple(
        _measurement_record(
            "align_measurements",
            axis_id="A01",
            subject=MeasurementSubject(MeasurementScope.SAMPLE, "Image"),
            rows=(
                {
                    "slice_index": 0,
                    "source_image_name": "Stain2",
                    "feature_name": "Align_Xshift_Stain2",
                    "result_value": shift,
                },
            ),
            group_component=Microscopy.Site,
            group_key=site,
        )
        for site, shift in (("1", -1.0), ("2", -2.0))
    )
    batch = RuntimeArtifactBatch(
        input_specs=(
            ArtifactSpec.input("align_measurements", MeasurementsArtifactType),
        ),
        records_by_axis={"A01": records},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    bundle = render_spreadsheet_bundle(
        add_filename_prefix=False,
        artifact_batch=batch,
    )

    assert tuple(csv.DictReader(io.StringIO(bundle["Image.csv"]))) == (
        {"image_number": "1", "Align_Xshift_Stain2": "-1.0"},
        {"image_number": "2", "Align_Xshift_Stain2": "-2.0"},
    )


def test_export_to_spreadsheet_uses_declared_image_set_identity_across_channels() -> (
    None
):
    image_record = _measurement_record(
        "image_measurements",
        axis_id="A01",
        subject=MeasurementSubject(MeasurementScope.SAMPLE, "Image"),
        rows=({"slice_index": 0, "Count": 2},),
        group_component=Microscopy.Channel,
        group_key="1",
        variable_components=(Microscopy.Site,),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            component_metadata=({"site": "1", "channel": "1"},)
        ),
    )
    object_record = _measurement_record(
        "cell_measurements",
        axis_id="A01",
        subject=MeasurementSubject(
            MeasurementScope.OBJECT,
            "Cells",
            "object_number",
        ),
        rows=({"slice_index": 0, "object_number": 1, "Area": 4.0},),
        group_component=Microscopy.Channel,
        group_key="2",
        variable_components=(Microscopy.Site,),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            component_metadata=({"site": "1", "channel": "2"},)
        ),
    )
    batch = RuntimeArtifactBatch(
        input_specs=(
            ArtifactSpec.input("image_measurements", MeasurementsArtifactType),
            ArtifactSpec.input("cell_measurements", MeasurementsArtifactType),
        ),
        records_by_axis={"A01": (image_record, object_record)},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(
            frozenset((Microscopy.Channel,))
        ),
    )

    bundle = render_spreadsheet_bundle(
        calculate_aggregate_means=True,
        add_filename_prefix=False,
        artifact_batch=batch,
    )

    assert tuple(csv.DictReader(io.StringIO(bundle["Image.csv"]))) == (
        {
            "image_number": "1",
            "Count": "2",
            "Mean_Cells_Area": "4.0",
        },
    )
    assert tuple(csv.DictReader(io.StringIO(bundle["Cells.csv"]))) == (
        {"image_number": "1", "object_number": "1", "Area": "4.0"},
    )


def test_export_to_spreadsheet_pairs_fully_addressed_field_measurements() -> None:
    """A biological address is not a declaration to stack every addressed axis."""
    bindings = SourceBindingsConfig(
        bindings=tuple(
            NamedSourceBinding(
                alias=alias,
                component_identity=tuple(
                    ComponentSelector(component, value)
                    for component, value in (
                        (Microscopy.Well, "A01"),
                        (Microscopy.Site, "1"),
                        (Microscopy.Channel, channel),
                        (Microscopy.ZIndex, "1"),
                        (Microscopy.Timepoint, "1"),
                    )
                ),
            )
            for alias, channel in (("DNA", "1"), ("Actin", "2"))
        )
    )
    policy = SourceImageSetIdentityPolicy.from_source_bindings(
        bindings,
        group_component=Microscopy.Channel,
    )
    records = []
    # Two independent fields, each with two cells. Local slice/object IDs repeat
    # intentionally: provenance, not runtime row position, owns field identity.
    for site in ("1", "2"):
        for channel, features in (
            ("1", {"Parent_Nuclei": 1, "Location_Center_X": 1.5}),
            ("2", {"AreaShape_Area": 4.0}),
        ):
            provenance = SourceImageProvenancePlanes.from_components(
                paths=(f"/synthetic/A01-field{site}-plane{channel}.tif",),
                component_metadata=(
                    {
                        "well": "A01",
                        "site": site,
                        "channel": channel,
                        "z_index": "1",
                        "timepoint": "1",
                    },
                ),
            )
            records.append(
                _measurement_record(
                    f"field{site}_plane{channel}",
                    axis_id="A01",
                    subject=MeasurementSubject(
                        MeasurementScope.OBJECT, "Cells", "object_number"
                    ),
                    rows=tuple(
                        {"slice_index": 0, "object_number": number, **features}
                        for number in (1, 2)
                    ),
                    source_image_provenance_planes=provenance,
                    group_component=Microscopy.Channel,
                    group_key=channel,
                    variable_components=(Microscopy.Site,),
                )
            )
        records.append(
            _measurement_record(
                f"field{site}_counts",
                axis_id="A01",
                subject=MeasurementSubject(MeasurementScope.SAMPLE, "Image"),
                rows=({"slice_index": 0, "Count_Cells": 2},),
                source_image_provenance_planes=provenance,
                group_component=Microscopy.Channel,
                group_key="2",
                variable_components=(Microscopy.Site,),
            )
        )
    batch = RuntimeArtifactBatch(
        input_specs=tuple(
            ArtifactSpec.input(record.key.name, MeasurementsArtifactType)
            for record in records
        ),
        records_by_axis={"A01": tuple(records)},
        source_image_set_identity_policy=policy,
    )

    bundle = render_spreadsheet_bundle(add_filename_prefix=False, artifact_batch=batch)

    cells = tuple(csv.DictReader(io.StringIO(bundle["Cells.csv"])))
    assert cells == tuple(
        {
            "image_number": image_number,
            "object_number": object_number,
            "Parent_Nuclei": "1",
            "Location_Center_X": "1.5",
            "AreaShape_Area": "4.0",
        }
        for image_number in ("1", "2")
        for object_number in ("1", "2")
    )
    assert tuple(csv.DictReader(io.StringIO(bundle["Image.csv"]))) == (
        {"image_number": "1", "Count_Cells": "2"},
        {"image_number": "2", "Count_Cells": "2"},
    )


def test_export_to_spreadsheet_nulls_metadata_that_differs_between_image_planes() -> (
    None
):
    records = tuple(
        _measurement_record(
            f"channel_{channel}_measurements",
            axis_id="A01",
            subject=MeasurementSubject(MeasurementScope.SAMPLE, "Image"),
            rows=({"slice_index": 0, f"Count_{channel}": int(channel)},),
            group_component=Microscopy.Channel,
            group_key=channel,
            variable_components=(Microscopy.Site,),
            source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
                component_metadata=(
                    {
                        "site": "1",
                        "channel": channel,
                        DECLARED_SOURCE_METADATA_FIELD: {
                            "ChannelNumber": channel,
                            "Site": "1",
                        },
                    },
                )
            ),
        )
        for channel in ("1", "4")
    )
    batch = RuntimeArtifactBatch(
        input_specs=tuple(
            ArtifactSpec.input(record.key.name, MeasurementsArtifactType)
            for record in records
        ),
        records_by_axis={"A01": records},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(
            frozenset((Microscopy.Channel,))
        ),
    )

    bundle = render_spreadsheet_bundle(
        add_filename_prefix=False,
        artifact_batch=batch,
    )

    assert tuple(csv.DictReader(io.StringIO(bundle["Image.csv"]))) == (
        {
            "image_number": "1",
            "Count_1": "1",
            "Count_4": "4",
            "Metadata_ChannelNumber": "",
            "Metadata_Site": "1",
        },
    )


def test_export_to_spreadsheet_copies_native_metadata_and_qualified_file_names() -> (
    None
):
    image = _measurement_record(
        "image",
        axis_id="A01",
        subject=MeasurementSubject(MeasurementScope.SAMPLE, "Image"),
        rows=(
            {
                "slice_index": 0,
                "Metadata_Plate": "plate",
                "FileName_DNA": "dna.tif",
                "PathName_DNA": "/inputs",
                "Image_FileName_Membrane": "membrane.tif",
            },
        ),
    )
    cells = _measurement_record(
        "cells",
        axis_id="A01",
        subject=MeasurementSubject(MeasurementScope.OBJECT, "Cells", "object_number"),
        rows=({"slice_index": 0, "object_number": 1, "Area": 2.0},),
    )
    batch = RuntimeArtifactBatch(
        input_specs=tuple(
            ArtifactSpec.input(record.key.name, MeasurementsArtifactType)
            for record in (image, cells)
        ),
        records_by_axis={"A01": (image, cells)},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    bundle = render_spreadsheet_bundle(
        artifact_batch=batch,
        add_image_metadata=True,
        add_image_file_names=True,
        add_filename_prefix=False,
    )

    (row,) = csv.DictReader(io.StringIO(bundle["Cells.csv"]))
    assert row["Metadata_Plate"] == "plate"
    assert row["Image_FileName_DNA"] == "dna.tif"
    assert row["Image_PathName_DNA"] == "/inputs"
    assert row["Image_FileName_Membrane"] == "membrane.tif"
    assert not any(name.startswith("Image_Metadata_") for name in row)
    assert not any(name.startswith("Image_Image_") for name in row)


def test_combined_spreadsheet_retains_native_subject_headers_and_sparse_rows(
    tmp_path,
) -> None:
    from benchmark.equivalence.runtime import RuntimeTableSnapshot

    records = tuple(
        _measurement_record(
            name,
            axis_id="A01",
            subject=MeasurementSubject(MeasurementScope.OBJECT, name, "object_number"),
            rows=tuple(
                {"slice_index": 0, "object_number": i, "Area": value}
                for i, value in enumerate(values, 1)
            ),
        )
        for name, values in (("Cells", (2.0, 4.0)), ("Cells_inner", (3.0,)))
    )
    batch = RuntimeArtifactBatch(
        input_specs=tuple(
            ArtifactSpec.input(record.key.name, MeasurementsArtifactType)
            for record in records
        ),
        records_by_axis={"A01": records},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )
    bundle = render_spreadsheet_bundle(
        artifact_batch=batch,
        export_all_measurement_types=False,
        file_selections=(
            SpreadsheetFileSelection(("Cells", "Cells_inner"), "Combined.csv"),
        ),
        add_filename_prefix=False,
    )
    lines = tuple(tuple(row) for row in csv.reader(io.StringIO(bundle["Combined.csv"])))
    assert lines == (
        ("Image", "Cells", "Cells", "Cells_inner", "Cells_inner"),
        ("image_number", "object_number", "Area", "object_number", "Area"),
        ("1", "1", "2.0", "1", "3.0"),
        ("1", "2", "4.0", "", ""),
    )
    from openhcs.interop.cellprofiler.measurement_dialect import (
        CELLPROFILER_MEASUREMENT_DIALECT,
    )

    path = tmp_path / "Combined.csv"
    path.write_text(bundle["Combined.csv"])
    tables = RuntimeTableSnapshot.from_csv(path).measurement_tables(
        CELLPROFILER_MEASUREMENT_DIALECT
    )
    assert tuple(table.subject.name for table in tables) == (
        "Image",
        "Cells",
        "Cells_inner",
    )
    assert tuple(tables[1].rows.column_values("Area")) == ("2.0", "4.0")


def test_native_csv_header_rows_preserve_quoting_and_reject_wrong_width() -> None:
    from numbers import Real
    from openhcs.core._tabular_native import render_csv

    result = render_csv(
        ((3.0,),),
        ("raw",),
        1,
        ",",
        Real,
        True,
        (("Cells,inner",), ('Area"quoted\nname',)),
    )
    assert tuple(csv.reader(io.StringIO(result))) == (
        ["Cells,inner"],
        ['Area"quoted\nname'],
        ["3.0"],
    )
    with pytest.raises(ValueError, match="header width"):
        render_csv(((3.0,),), ("raw",), 1, ",", Real, True, (("one", "two"),))


def test_export_to_spreadsheet_merges_object_features_across_runtime_groups() -> None:
    provenance_by_channel = (
        SourceImageProvenancePlanes.from_components(
            component_metadata=({"site": "1", "channel": channel},)
        )
        for channel in ("1", "2")
    )
    records = tuple(
        _measurement_record(
            name,
            axis_id="A01",
            subject=MeasurementSubject(
                MeasurementScope.OBJECT,
                "Cells",
                "object_number",
            ),
            rows=(
                {
                    "slice_index": 0,
                    "object_number": 1,
                    feature_name: value,
                },
            ),
            group_component=Microscopy.Channel,
            group_key=channel,
            variable_components=(Microscopy.Site,),
            source_image_provenance_planes=provenance,
        )
        for name, channel, feature_name, value, provenance in zip(
            ("area_measurements", "perimeter_measurements"),
            ("1", "2"),
            ("Area", "Perimeter"),
            (4.0, 6.0),
            provenance_by_channel,
            strict=True,
        )
    )
    batch = RuntimeArtifactBatch(
        input_specs=tuple(
            ArtifactSpec.input(record.key.name, MeasurementsArtifactType)
            for record in records
        ),
        records_by_axis={"A01": records},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(
            frozenset((Microscopy.Channel,))
        ),
    )

    bundle = render_spreadsheet_bundle(
        add_filename_prefix=False,
        artifact_batch=batch,
    )

    assert tuple(csv.DictReader(io.StringIO(bundle["Cells.csv"]))) == (
        {
            "image_number": "1",
            "object_number": "1",
            "Area": "4.0",
            "Perimeter": "6.0",
        },
    )


def test_export_to_spreadsheet_aggregates_mixed_producer_declared_rows() -> None:
    producer_rows = (
        {"slice_index": 0, "Count_Tissue": 2},
        {
            "slice_index": 0,
            "object_name": "Tissue",
            "object_label": 1,
            "Location_Center_X": 4.0,
        },
        {
            "slice_index": 0,
            "object_name": "Tissue",
            "object_label": 2,
            "Location_Center_X": 8.0,
        },
    )
    record = _measurement_record(
        "identify_primary_objects_measurements",
        axis_id="A01",
        subject=MeasurementSubject(
            MeasurementScope.SAMPLE,
            MeasurementScope.SAMPLE.value,
        ),
        rows=producer_rows,
    )
    batch = RuntimeArtifactBatch(
        input_specs=(
            ArtifactSpec.input(
                "identify_primary_objects_measurements",
                MeasurementsArtifactType,
            ),
        ),
        records_by_axis={"A01": (record,)},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    bundle = render_spreadsheet_bundle(
        calculate_aggregate_means=True,
        add_filename_prefix=False,
        artifact_batch=batch,
    )

    assert tuple(csv.DictReader(io.StringIO(bundle["Image.csv"]))) == (
        {
            "image_number": "1",
            "Count_Tissue": "2",
            "Mean_Tissue_Location_Center_X": "6.0",
        },
    )


def test_export_to_spreadsheet_resolves_slice_indices_per_producer_table() -> None:
    records = tuple(
        _measurement_record(
            name,
            axis_id="A01",
            subject=MeasurementSubject(MeasurementScope.SAMPLE, "Image"),
            rows=({"slice_index": 0, feature: value},),
            source_image_provenance_planes=(
                SourceImageProvenancePlanes.from_components(
                    component_metadata=({"well": "A01", "site": site, "channel": "1"},)
                )
            ),
        )
        for name, feature, value, site in (
            ("first_measurements", "First", 1, "1"),
            ("second_measurements", "Second", 2, "2"),
        )
    )
    batch = RuntimeArtifactBatch(
        input_specs=tuple(
            ArtifactSpec.input(name, MeasurementsArtifactType)
            for name in ("first_measurements", "second_measurements")
        ),
        records_by_axis={"A01": records},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    bundle = render_spreadsheet_bundle(
        add_filename_prefix=False,
        artifact_batch=batch,
    )

    assert tuple(csv.DictReader(io.StringIO(bundle["Image.csv"]))) == (
        {"image_number": "1", "First": "1", "Second": ""},
        {"image_number": "2", "First": "", "Second": "2"},
    )


def test_export_to_spreadsheet_anchors_axisless_artifact_summary_to_stack() -> None:
    name = "neurite_outgrowth_summary"
    record = _measurement_record(
        name,
        axis_id="A01",
        subject=MeasurementSubject(MeasurementScope.ARTIFACT),
        rows=({"number_of_cells": 3, "total_outgrowth": 42.0},),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            component_metadata=(
                {"well": "A01", "site": "1", "channel": "4"},
                {"well": "A01", "site": "1", "channel": "1"},
            )
        ),
    )
    batch = RuntimeArtifactBatch(
        input_specs=(ArtifactSpec.input(name, MeasurementsArtifactType),),
        records_by_axis={"A01": (record,)},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    bundle = render_spreadsheet_bundle(
        add_filename_prefix=False,
        artifact_batch=batch,
    )

    assert tuple(csv.DictReader(io.StringIO(bundle[f"{name}.csv"]))) == (
        {
            "image_number": "1",
            "number_of_cells": "3",
            "total_outgrowth": "42.0",
        },
    )


def test_export_to_spreadsheet_rejects_axisless_artifact_without_source_identity() -> (
    None
):
    name = "unbound_artifact_summary"
    record = _measurement_record(
        name,
        axis_id="A01",
        subject=MeasurementSubject(MeasurementScope.ARTIFACT),
        rows=({"Count": 3},),
        source_image_provenance_planes=SourceImageProvenancePlanes(),
    )
    batch = RuntimeArtifactBatch(
        input_specs=(ArtifactSpec.input(name, MeasurementsArtifactType),),
        records_by_axis={"A01": (record,)},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    with pytest.raises(
        ValueError,
        match="requires .*producer-declared source identity",
    ):
        render_spreadsheet_bundle(
            add_filename_prefix=False,
            artifact_batch=batch,
        )


def test_export_to_spreadsheet_rejects_axisless_image_rows_across_image_sets() -> None:
    name = "ambiguous_image_summary"
    record = _measurement_record(
        name,
        axis_id="A01",
        subject=MeasurementSubject(MeasurementScope.SAMPLE, "Image"),
        rows=({"Count": 3},),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            component_metadata=(
                {"well": "A01", "site": "1", "channel": "4"},
                {"well": "A01", "site": "1", "channel": "1"},
            )
        ),
    )
    batch = RuntimeArtifactBatch(
        input_specs=(ArtifactSpec.input(name, MeasurementsArtifactType),),
        records_by_axis={"A01": (record,)},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    with pytest.raises(
        ValueError,
        match="cannot bind axisless rows.*image numbers \\(1, 2\\)",
    ):
        render_spreadsheet_bundle(
            add_filename_prefix=False,
            artifact_batch=batch,
        )


def test_export_to_spreadsheet_binds_payload_rows_to_exact_source_image_set() -> None:
    batch = RuntimeArtifactBatch(
        input_specs=(
            ArtifactSpec.input("object_measurements", MeasurementsArtifactType),
        ),
        records_by_axis={
            "A01": (
                _measurement_record(
                    "object_measurements",
                    axis_id="A01",
                    subject=MeasurementSubject(MeasurementScope.OBJECT, "Cells"),
                    rows=(
                        {
                            "slice_index": 0,
                            "object_name": "Cells",
                            "object_label": 1,
                            "Area": 4.0,
                        },
                        {
                            "slice_index": 0,
                            "object_name": "Cells",
                            "object_label": 1,
                            "Children_Nuclei_Count": 1,
                        },
                    ),
                ),
            )
        },
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    bundle = render_spreadsheet_bundle(
        add_filename_prefix=False,
        artifact_batch=batch,
    )

    assert tuple(csv.DictReader(io.StringIO(bundle["Cells.csv"]))) == (
        {
            "image_number": "1",
            "object_number": "1",
            "Area": "4.0",
            "Children_Nuclei_Count": "1",
        },
    )


def test_export_to_spreadsheet_aggregate_requires_declared_image_row() -> None:
    batch = RuntimeArtifactBatch(
        input_specs=(ArtifactSpec.input("cells", MeasurementsArtifactType),),
        records_by_axis={
            "A01": (
                _measurement_record(
                    "cells",
                    axis_id="A01",
                    subject=MeasurementSubject(
                        MeasurementScope.OBJECT,
                        "Cells",
                        "object_number",
                    ),
                    rows=({"slice_index": 0, "object_number": 1, "Area": 2.0},),
                ),
            )
        },
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    with pytest.raises(
        ValueError,
        match="producer-declared Image measurement row for image_number=1",
    ):
        render_spreadsheet_bundle(
            calculate_aggregate_means=True,
            add_filename_prefix=False,
            artifact_batch=batch,
        )


def test_export_to_spreadsheet_preserves_source_qualified_wide_features() -> None:
    source_values = (("BF_image", 82.5), ("Marker_image", 52.75))
    records = tuple(
        _measurement_record(
            "granularity_measurements",
            axis_id="A01",
            subject=MeasurementSubject(MeasurementScope.OBJECT, "Cells"),
            source_image_name=source_image_name,
            rows=(
                {
                    "slice_index": 0,
                    "object_id": 1,
                    f"Granularity_1_{source_image_name}": value,
                },
            ),
        )
        for source_image_name, value in source_values
    )
    batch = RuntimeArtifactBatch(
        input_specs=(
            ArtifactSpec.input("granularity_measurements", MeasurementsArtifactType),
        ),
        records_by_axis={"A01": records},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    bundle = render_spreadsheet_bundle(
        add_filename_prefix=False,
        artifact_batch=batch,
    )

    rows = tuple(csv.DictReader(io.StringIO(bundle["Cells.csv"])))
    assert rows == (
        {
            "image_number": "1",
            "object_number": "1",
            **{
                f"Granularity_1_{source_image_name}": str(value)
                for source_image_name, value in source_values
            },
        },
    )


def test_export_to_spreadsheet_keeps_crop_outputs_distinct_at_same_slice_index() -> (
    None
):
    crop_values = (("CropedWormsImage", 80, 100), ("CropBlue", 20, 50))
    records = tuple(
        _measurement_record(
            f"{source_image_name}_crop_measurements",
            axis_id="A01",
            subject=MeasurementSubject(MeasurementScope.SAMPLE, "Image"),
            source_image_name=source_image_name,
            rows=CropModule.prepare_measurement_record_rows(
                MeasurementSparseColumnarRows.from_rows(
                    (
                        {
                            "slice_index": 0,
                            "area_retained": area_retained,
                            "original_area": original_area,
                            "fraction_retained": area_retained / original_area,
                        },
                    ),
                    fields=(
                        FieldSpec("slice_index", int),
                        FieldSpec("area_retained", int),
                        FieldSpec("original_area", int),
                        FieldSpec("fraction_retained", float),
                    ),
                ),
                source_image_name=source_image_name,
            ),
        )
        for source_image_name, area_retained, original_area in crop_values
    )
    batch = RuntimeArtifactBatch(
        input_specs=tuple(
            ArtifactSpec.input(
                f"{source_image_name}_crop_measurements",
                MeasurementsArtifactType,
            )
            for source_image_name, _area_retained, _original_area in crop_values
        ),
        records_by_axis={"A01": records},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    bundle = render_spreadsheet_bundle(
        add_filename_prefix=False,
        artifact_batch=batch,
    )

    rows = tuple(csv.DictReader(io.StringIO(bundle["Image.csv"])))
    assert rows == (
        {
            "image_number": "1",
            "Crop_AreaRetainedAfterCropping_CropedWormsImage": "80",
            "Crop_OriginalImageArea_CropedWormsImage": "100",
            "Crop_AreaRetainedAfterCropping_CropBlue": "20",
            "Crop_OriginalImageArea_CropBlue": "50",
        },
    )


def test_export_to_spreadsheet_preserves_declared_intensity_feature() -> None:
    feature_name = (
        "_".join(
            (
                *MeasureObjectIntensityModule.measurement_category_prefixes[0],
                MeasureObjectIntensityModule.MeasurementFeature.MEAN_INTENSITY.value,
            )
        )
        + "_DNA"
    )
    batch = RuntimeArtifactBatch(
        input_specs=(
            ArtifactSpec.input("intensity_measurements", MeasurementsArtifactType),
        ),
        records_by_axis={
            "A01": (
                _measurement_record(
                    "intensity_measurements",
                    axis_id="A01",
                    subject=MeasurementSubject(MeasurementScope.OBJECT, "Cells"),
                    source_image_name="DNA",
                    rows=(
                        {
                            "slice_index": 0,
                            "object_id": 1,
                            feature_name: 12.5,
                        },
                    ),
                ),
            )
        },
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    bundle = render_spreadsheet_bundle(
        add_filename_prefix=False,
        artifact_batch=batch,
    )

    rows = tuple(csv.DictReader(io.StringIO(bundle["Cells.csv"])))
    assert rows == (
        {
            "image_number": "1",
            "object_number": "1",
            feature_name: "12.5",
        },
    )


def test_export_to_spreadsheet_leaves_track_objects_features_unsuffixed() -> None:
    object_feature = TrackObjectsModule.measurement_feature_name("displacement")
    image_feature = TrackObjectsModule.measurement_feature_name(
        "new_object_count",
        "Cells",
    )
    records = (
        _measurement_record(
            "tracking_object_measurements",
            axis_id="A01",
            subject=MeasurementSubject(MeasurementScope.OBJECT, "Cells"),
            source_image_name="DNA",
            rows=(
                {
                    "slice_index": 0,
                    "object_id": 1,
                    object_feature: 4.25,
                },
            ),
        ),
        _measurement_record(
            "tracking_image_measurements",
            axis_id="A01",
            subject=MeasurementSubject(MeasurementScope.SAMPLE, "Image"),
            source_image_name="DNA",
            rows=({"slice_index": 0, image_feature: 3},),
        ),
    )
    batch = RuntimeArtifactBatch(
        input_specs=tuple(
            ArtifactSpec.input(name, MeasurementsArtifactType)
            for name in (
                "tracking_object_measurements",
                "tracking_image_measurements",
            )
        ),
        records_by_axis={"A01": records},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    bundle = render_spreadsheet_bundle(
        add_filename_prefix=False,
        artifact_batch=batch,
    )

    assert tuple(csv.DictReader(io.StringIO(bundle["Cells.csv"]))) == (
        {
            "image_number": "1",
            "object_number": "1",
            object_feature: "4.25",
        },
    )
    assert tuple(csv.DictReader(io.StringIO(bundle["Image.csv"]))) == (
        {"image_number": "1", image_feature: "3"},
    )


def test_export_to_spreadsheet_leaves_worm_descriptor_fields_unsuffixed() -> None:
    descriptor_field = WormControlPointMeasurementField(
        WormControlPointAxis.COLUMN,
        1,
    ).name
    batch = RuntimeArtifactBatch(
        input_specs=(
            ArtifactSpec.input("worm_measurements", MeasurementsArtifactType),
        ),
        records_by_axis={
            "A01": (
                _measurement_record(
                    "worm_measurements",
                    axis_id="A01",
                    subject=MeasurementSubject(MeasurementScope.OBJECT, "Worms"),
                    source_image_name="BinaryWorms",
                    rows=(
                        {
                            "slice_index": 0,
                            "object_number": 1,
                            descriptor_field: 17.5,
                        },
                    ),
                ),
            )
        },
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    bundle = render_spreadsheet_bundle(
        add_filename_prefix=False,
        artifact_batch=batch,
    )

    assert tuple(csv.DictReader(io.StringIO(bundle["Worms.csv"]))) == (
        {
            "image_number": "1",
            "object_number": "1",
            descriptor_field: "17.5",
        },
    )


def test_export_to_spreadsheet_folds_descriptor_axes_before_coalescing() -> None:
    batch = RuntimeArtifactBatch(
        input_specs=(
            ArtifactSpec.input("texture_measurements", MeasurementsArtifactType),
        ),
        records_by_axis={
            "A01": (
                _measurement_record(
                    "texture_measurements",
                    axis_id="A01",
                    subject=MeasurementSubject(MeasurementScope.OBJECT, "Cells"),
                    source_image_name="BF_image",
                    rows=tuple(
                        {
                            "slice_index": 0,
                            "object_id": 1,
                            "scale": 3,
                            "direction": direction,
                            "gray_levels": 256,
                            "axis": {
                                "slice_index": 0,
                                "scale": 3,
                                "direction": direction,
                                "gray_levels": 256,
                            },
                            "Texture_Contrast_BF_image": value,
                        }
                        for direction, value in ((0, 0.25), (1, 0.75))
                    ),
                ),
            )
        },
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    bundle = render_spreadsheet_bundle(
        add_filename_prefix=False,
        artifact_batch=batch,
    )

    rows = tuple(csv.DictReader(io.StringIO(bundle["Cells.csv"])))
    assert len(rows) == 1
    assert rows[0]["Texture_Contrast_BF_image_3_00_256"] == "0.25"
    assert rows[0]["Texture_Contrast_BF_image_3_01_256"] == "0.75"
    assert "axis" not in rows[0]


def test_export_to_spreadsheet_folds_neighbor_scale_once() -> None:
    image_record = _measurement_record(
        "image_measurements",
        axis_id="A01",
        subject=MeasurementSubject(MeasurementScope.SAMPLE, "Image"),
        rows=({"slice_index": 0, "Count_Cells": 1},),
    )
    neighbor_record = _measurement_record(
        "neighbor_measurements",
        axis_id="A01",
        subject=MeasurementSubject(MeasurementScope.OBJECT, "Cells", "object_id"),
        rows=(
            {
                "slice_index": 0,
                "object_id": 1,
                "scale": "expanded",
                "feature_name": "Neighbors_NumberOfNeighbors",
                "measurement_value": 2,
            },
        ),
    )
    batch = RuntimeArtifactBatch(
        input_specs=(
            ArtifactSpec.input("image_measurements", MeasurementsArtifactType),
            ArtifactSpec.input("neighbor_measurements", MeasurementsArtifactType),
        ),
        records_by_axis={"A01": (image_record, neighbor_record)},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    bundle = render_spreadsheet_bundle(
        calculate_aggregate_means=True,
        add_filename_prefix=False,
        artifact_batch=batch,
    )

    assert tuple(csv.DictReader(io.StringIO(bundle["Cells.csv"]))) == (
        {
            "image_number": "1",
            "object_number": "1",
            "Neighbors_NumberOfNeighbors_expanded": "2",
        },
    )
    assert tuple(csv.DictReader(io.StringIO(bundle["Image.csv"]))) == (
        {
            "image_number": "1",
            "Count_Cells": "1",
            "Mean_Cells_Neighbors_NumberOfNeighbors_expanded": "2.0",
        },
    )


def test_export_to_spreadsheet_routes_row_owned_objects_and_normalizes_ids() -> None:
    batch = RuntimeArtifactBatch(
        input_specs=(
            ArtifactSpec.input("mixed_measurements", MeasurementsArtifactType),
        ),
        records_by_axis={
            "A01": (
                _measurement_record(
                    "mixed_measurements",
                    axis_id="A01",
                    subject=MeasurementSubject(MeasurementScope.SAMPLE, "Image"),
                    rows=(
                        {
                            "slice_index": 0,
                            "object_id": 1,
                            "object_name": "Cells",
                            "openhcs_object_row_identity": "row_ordinal",
                            "Area": 2.0,
                        },
                        {
                            "slice_index": 0,
                            "object_label": 1,
                            "object_name": "Cells",
                            "Perimeter": 3.0,
                        },
                    ),
                ),
            )
        },
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    bundle = render_spreadsheet_bundle(
        add_filename_prefix=False,
        artifact_batch=batch,
    )

    rows = tuple(csv.DictReader(io.StringIO(bundle["Cells.csv"])))
    assert rows == (
        {
            "image_number": "1",
            "object_number": "1",
            "Area": "2.0",
            "Perimeter": "3.0",
        },
    )


def _module(rows: tuple[tuple[str, str], ...]) -> ModuleBlock:
    records = [ModuleSetting(name, value) for name, value in rows]
    return ModuleBlock(
        name="ExportToSpreadsheet",
        module_num=7,
        setting_records=records,
    )


def _measurement_record(
    name: str,
    *,
    axis_id: str,
    subject: MeasurementSubject,
    rows: tuple[dict[str, object], ...] | ColumnarRows,
    source_image_name: str | None = None,
    source_image_provenance_planes: SourceImageProvenancePlanes | None = None,
    group_component: type[Axis] | None = None,
    group_key: str | None = None,
    variable_components: tuple[type[Axis], ...] = (),
) -> StoredRuntimeValue:
    if not isinstance(rows, ColumnarRows):
        field_names = tuple(
            dict.fromkeys(field_name for row in rows for field_name in row)
        )
        rows = MeasurementSparseColumnarRows.from_rows(
            rows,
            fields=tuple(
                FieldSpec(
                    field_name,
                    _fixture_field_dtype(rows, field_name),
                )
                for field_name in field_names
            ),
        )
    if source_image_provenance_planes is None:
        slice_indices = tuple(
            dict.fromkeys(
                int(row["slice_index"])
                for row in rows.iter_row_mappings()
                if "slice_index" in row
            )
        )
        source_image_provenance_planes = SourceImageProvenancePlanes.from_components(
            component_metadata=tuple(
                {
                    **(
                        {group_component.name: group_key}
                        if group_component is not None and group_key is not None
                        else {}
                    ),
                    **(
                        {Microscopy.Site.name: str(slice_index + 1)}
                        if group_component is not Microscopy.Site
                        else {}
                    ),
                }
                for slice_index in slice_indices
            )
        )
    output_plan = ArtifactOutputPlan(
        name=name,
        path=f"/memory/{name}.pkl",
        artifact_type=MeasurementsArtifactType,
        group_keys=(group_key,),
        group_component=group_component,
        variable_components=variable_components,
    )
    value = RuntimeValue.normalize(
        output_plan,
        MeasurementTable(
            name=name,
            rows=rows,
            subject=subject,
            source_image_name=source_image_name,
            source_image_provenance_planes=source_image_provenance_planes,
        ),
        axis_id=axis_id,
    )
    return StoredRuntimeValue(
               key=value.key,
               data=value.data,
               materialization_source_metadata=value.materialization_source_metadata,
               location=RuntimeArtifactLocation(path=output_plan.path, backend="memory"),
           )


def _fixture_field_dtype(
    rows: tuple[dict[str, object], ...],
    field_name: str,
) -> type[object]:
    field_types = tuple(
        dict.fromkeys(type(row[field_name]) for row in rows if field_name in row)
    )
    if len(field_types) != 1:
        raise TypeError(
            f"Fixture field {field_name!r} requires one exact scalar type, "
            f"got {field_types!r}."
        )
    return field_types[0]


def _relationship_record(name: str, *, axis_id: str) -> StoredRuntimeValue:
    output_plan = ArtifactOutputPlan(
        name=name,
        path=f"/memory/{name}.pkl",
        artifact_type=RelationshipsArtifactType,
    )
    value = RuntimeValue.normalize(
        output_plan,
        ObjectRelationship(
            name=name,
            declaration=ObjectRelationshipDeclaration(
                source=ArtifactSpec.output("Parents", ObjectLabelsArtifactType).ref(),
                target=ArtifactSpec.output("Children", ObjectLabelsArtifactType).ref(),
                relationship_type="related",
                source_role="parent",
                target_role="child",
                source_id_field="parent_number",
                target_id_field="child_number",
                producer_module_number=1,
                source_runtime_slice_offset=0,
                target_runtime_slice_offset=0,
            ),
            payload=DirectedObjectRelationshipPayload(
                source_ids=(1,), target_ids=(2,), slice_indices=(), slice_count=None
            ),
        ),
        axis_id=axis_id,
    )
    return StoredRuntimeValue(
               key=value.key,
               data=value.data,
               materialization_source_metadata=value.materialization_source_metadata,
               location=RuntimeArtifactLocation(path=output_plan.path, backend="memory"),
           )


@pytest.mark.parametrize("cycle_aligned", (False, True))
def test_spatial_grid_geometry_is_exported_for_exact_source_cycles(
    cycle_aligned: bool,
) -> None:
    from openhcs.core.runtime_spatial_grid import SpatialGrid, SpatialGridAxis
    from openhcs.core.runtime_slice_alignment import RuntimeSliceAlignedValues
    from openhcs.core.runtime_artifact_queries import (
        RuntimeArtifactQueryContext,
        runtime_measurement_tables,
    )
    from openhcs.core.runtime_stores import RuntimeValueStore

    provenance = SourceImageProvenance(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/inputs/site2.tif", "/inputs/site1.tif"),
            component_metadata=({"site": "2"}, {"site": "1"}),
        ),
    )
    grid = SpatialGrid(
        name="Grid",
        rows=8,
        columns=12,
        x_spacing=102.5,
        y_spacing=103.25,
        x_origin=71,
        y_origin=57,
        source_provenance=provenance,
    )
    data = (
        RuntimeSliceAlignedValues(
            (
                grid,
                grid.replace_fields(
                    column_axis=SpatialGridAxis(spacing=102.5, origin=72).normalized(
                        12, "column_axis"
                    )
                ),
            )
        )
        if cycle_aligned
        else grid
    )
    plan = ArtifactOutputPlan(
        name="Grid", path="/memory/Grid.pkl", artifact_type=SpatialGridArtifactType
    )
    value = RuntimeValue.normalize(plan, data, axis_id="A01")
    store = RuntimeValueStore()
    record = store.record(value, path=plan.path, backend="memory")
    batch = RuntimeArtifactBatch(
        input_specs=(ArtifactSpec.input("Grid", SpatialGridArtifactType),),
        records_by_axis={"A01": (record,)},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )
    bundle = render_spreadsheet_bundle(
        delimiter=SpreadsheetDelimiter.COMMA,
        add_filename_prefix=False,
        artifact_batch=batch,
        file_selections=(SpreadsheetFileSelection(("Image",), "Image.csv"),),
    )
    rows = tuple(csv.DictReader(io.StringIO(bundle["Image.csv"])))
    assert [row["image_number"] for row in rows] == ["1", "2"]
    assert [float(row["DefinedGrid_Grid_XLocationOfLowestXSpot"]) for row in rows] == [
        71,
        72 if cycle_aligned else 71,
    ]
    for row in rows:
        assert float(row["DefinedGrid_Grid_Columns"]) == 12
        assert float(row["DefinedGrid_Grid_Rows"]) == 8
        assert float(row["DefinedGrid_Grid_XSpacing"]) == 102.5
        assert float(row["DefinedGrid_Grid_YLocationOfLowestYSpot"]) == 57
        assert float(row["DefinedGrid_Grid_YSpacing"]) == 103.25
    context = RuntimeArtifactQueryContext(store, "A01")
    assert runtime_measurement_tables(context)
    grid.column_axis = SpatialGridAxis(spacing=102.5, origin=73).normalized(
        12, "column_axis"
    )
    assert all(
        float(row["spatial_grid_grid_x_origin"]) == 73
        for row in runtime_measurement_tables(context)[0].iter_row_mappings()
    )
    materialized = SpatialGridArtifactType.materialization_payload(value)
    restored = SpatialGridArtifactType.normalize_runtime_payload("Grid", materialized)
    restored_grid = restored.value_at(0) if cycle_aligned else restored
    assert (
        restored_grid.source_provenance.equality_identity
        == grid.source_provenance.equality_identity
    )


@pytest.mark.parametrize("long_form", (False, True))
@pytest.mark.parametrize("concatenated", (False, True))
def test_image_number_references_follow_exact_source_numbering(
    long_form: bool, concatenated: bool
) -> None:
    from openhcs.interop.cellprofiler.image_set_numbering import (
        CellProfilerImageSetNumbering,
    )
    from openhcs.core.component_group_scope import RuntimeExecutionAxisScope

    provenance = SourceImageProvenancePlanes.from_components(
        paths=("/inputs/first.tif", "/inputs/second.tif", "/inputs/third.tif"),
        component_metadata=({"site": "1"}, {"site": "2"}, {"site": "3"}),
    )
    values = (0, 1, 2, float("nan"), float("inf"), MEASUREMENT_SPARSE_CELL)
    reference_name = "Tracking_ParentImageNumber_50"
    columns = {"slice_index": (2,) * len(values), "object_number": tuple(range(1, 7))}
    if long_form:
        columns.update(
            feature_name=(reference_name,) * len(values), measurement_value=values
        )
        value_column = "measurement_value"
    else:
        columns[reference_name] = values
        value_column = reference_name
    from openhcs.core.measurement_row_materialization import ConcatenatedColumnarRows

    fields = tuple(
        FieldSpec(name, int)
        if name in ("slice_index", "object_number")
        else FieldSpec(name, required=False)
        for name in columns
    )
    source_rows = (
        ConcatenatedColumnarRows(tuple(
            MeasurementSparseColumnarRows(
                {name: values[start:start + 3] for name, values in columns.items()},
                fields=fields,
            )
            for start in (0, 3)
        ))
        if concatenated
        else MeasurementSparseColumnarRows(columns, fields=fields)
    )
    record = _measurement_record(
        "references",
        axis_id="A01",
        subject=MeasurementSubject(MeasurementScope.OBJECT, "Cells", "object_number"),
        rows=source_rows,
        source_image_provenance_planes=provenance,
    )
    table = record.data
    numbering = CellProfilerImageSetNumbering(SourceImageSetIdentityPolicy())
    scope = RuntimeExecutionAxisScope("A01")
    numbering.for_source_slices(
        scope=scope,
        provenance=table.source_provenance,
        slice_indices=(1, 0),
        owner=table.name,
    )
    projected = numbering.project_measurement_rows(scope=scope, table=table)
    actual = projected.column_values(value_column)
    assert tuple(actual[:3]) == (0, 2, 1)
    assert math.isnan(actual[3])
    assert math.isinf(actual[4])
    assert actual[5] is MEASUREMENT_SPARSE_CELL
    assert tuple(table.rows.column_values(value_column)) == values
    assert (
        projected.covers_declared_object_measurement_domain
        == table.rows.covers_declared_object_measurement_domain
    )


def test_declared_reference_mean_uses_full_projected_objects_after_selection() -> None:
    from openhcs.processing.backends.cellprofiler.spreadsheet_export import (
        _with_requested_aggregates,
    )

    def columns(**values):
        return MeasurementSparseColumnarRows(
            values,
            fields=tuple(FieldSpec(name, required=False) for name in values),
        )

    name = "Mean_Cells_Tracking_ParentImageNumber_50"
    source = OrderedDict(
        Image=columns(image_number=(23,), **{name: (0.5,)}),
        Cells=columns(
            image_number=(23, 23), Tracking_ParentImageNumber_50=(0, 22)
        ),
    )
    selected = OrderedDict(Image=source["Image"])
    result = _with_requested_aggregates(
        selected,
        object_subjects=("Cells",),
        mean=False,
        median=False,
        standard_deviation=False,
        source_tables=source,
    )
    assert result["Image"].column_values(name)[0] == 11
    assert source["Image"].column_values(name)[0] == 0.5


@pytest.mark.parametrize(
    "selection_mode", ("ordinary", "combined", "relationships", "experiment", "all")
)
def test_partitioned_export_admits_only_consumed_relationship_subject(selection_mode):
    from openhcs.processing.backends.cellprofiler.image_quality import (
        MeasureImageQualityModule,
    )
    from openhcs.core.runtime_batch_contracts import (
        RuntimeArtifactPartitionBatchRequest,
    )
    from openhcs.processing.backends.cellprofiler.spreadsheet_export import (
        _partitioned_spreadsheet_export,
    )
    from openhcs.processing.materialization.core import ColumnarCsvOutput

    records = {}
    for ordinal in range(1, 13):
        axis = f"W{ordinal:03d}"
        records[axis] = (
            _measurement_record(
                "images",
                axis_id=axis,
                subject=MeasurementSubject(MeasurementScope.SAMPLE, "Image"),
                rows=(
                    {
                        "slice_index": 0,
                        "Count": 2,
                        "ImageQuality_ThresholdOtsu_OrigRed_2W": ordinal / 20,
                    },
                ),
            ),
            _measurement_record(
                "cells",
                axis_id=axis,
                subject=MeasurementSubject(
                    MeasurementScope.OBJECT, "Cells", "object_number"
                ),
                rows=(
                    {"slice_index": 0, "object_number": 1, "Area": 2.0},
                    {"slice_index": 0, "object_number": 2, "Area": 4.0},
                ),
            ),
            _relationship_record("relationships", axis_id=axis),
        )
        records[axis][0].data.measurement_feature_owner = MeasureImageQualityModule
    batch = RuntimeArtifactBatch(
        input_specs=(
            ArtifactSpec.input("images", MeasurementsArtifactType),
            ArtifactSpec.input("cells", MeasurementsArtifactType),
            ArtifactSpec.input("relationships", RelationshipsArtifactType),
        ),
        records_by_axis=records,
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )
    selections = (
        (SpreadsheetFileSelection(("Image", "Cells"), "Combined.csv"),)
        if selection_mode == "combined"
        else (
            SpreadsheetFileSelection(("Image",), "Image.csv"),
            SpreadsheetFileSelection(("Cells",), "Cells.csv"),
        )
    )
    if selection_mode == "relationships":
        selections += (
            SpreadsheetFileSelection(("Object relationships",), "Edges.csv"),
        )
    if selection_mode == "experiment":
        selections += (SpreadsheetFileSelection(("Experiment",), "Experiment.csv"),)
    kwargs = dict(
        export_all_measurement_types=selection_mode == "all",
        file_selections=selections,
        calculate_aggregate_means=True,
        add_filename_prefix=False,
    )
    expected = render_spreadsheet_bundle(batch, **kwargs)
    mapped = []

    def map_partitions(func, requests):
        mapped.extend(requests)
        return tuple(func(request) for request in requests)

    request = RuntimeArtifactPartitionBatchRequest.from_contract(
        CallableContract.from_callable(export_to_spreadsheet),
        artifact_batch=batch,
        kwargs=kwargs,
        runtime_context=None,
        map_partition_invocations=map_partitions,
    )
    outputs = _partitioned_spreadsheet_export(request)
    actual = {
        path: (
            output.rendered() if isinstance(output, ColumnarCsvOutput) else output
        ).require_text_content()
        for path, output in outputs.items()
    }
    assert actual == expected
    assert len(mapped) == (
        0 if selection_mode in ("relationships", "experiment", "all") else 12
    )


@pytest.mark.parametrize("overlapping_declarations", (False, True))
def test_partitioned_relationship_export_preserves_producer_then_axis_order(
    overlapping_declarations: bool,
) -> None:
    from dataclasses import replace
    from openhcs.processing.materialization.core import ColumnarCsvOutput
    from openhcs.core.runtime_batch_contracts import (
        RuntimeArtifactPartitionBatchRequest,
    )
    from openhcs.processing.backends.cellprofiler.spreadsheet_export import (
        _partitioned_spreadsheet_export,
    )

    records = {}
    for axis in ("W001", "W002"):
        image = _measurement_record(
            "images",
            axis_id=axis,
            subject=MeasurementSubject(MeasurementScope.SAMPLE, "Image"),
            rows=({"slice_index": 0, "Count": 2},),
        )
        edges = []
        for ordinal, name in enumerate(("parents", "children"), 1):
            record = _relationship_record(name, axis_id=axis)
            declaration = replace(
                record.data.declaration,
                producer_module_number=1 if overlapping_declarations else ordinal,
                source_id_field="parent_number" if ordinal == 1 else "child_number",
                target_id_field="child_number" if ordinal == 1 else "parent_number",
            )
            relationship = ObjectRelationship.from_payload(
                name=name,
                declaration=declaration,
                payload=DirectedObjectRelationshipPayload(
                    source_ids=(1,),
                    target_ids=(2,),
                    slice_indices=(0,),
                    slice_count=1,
                ),
                source_provenance=image.data.source_provenance,
            )
            edges.append(replace(record, data=relationship))
        records[axis] = (image, *edges)
    batch = RuntimeArtifactBatch(
        input_specs=(
            ArtifactSpec.input("images", MeasurementsArtifactType),
            ArtifactSpec.input("parents", RelationshipsArtifactType),
            ArtifactSpec.input("children", RelationshipsArtifactType),
        ),
        records_by_axis=records,
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )
    kwargs = dict(
        export_all_measurement_types=False,
        file_selections=(
            SpreadsheetFileSelection(("Image",), "Image.csv"),
            SpreadsheetFileSelection(("Object relationships",), "Edges.csv"),
        ),
        add_filename_prefix=False,
    )
    expected = render_spreadsheet_bundle(batch, **kwargs)
    mapped = []

    def map_partitions(func, requests):
        mapped.extend(requests)
        return tuple(func(request) for request in requests)

    request = RuntimeArtifactPartitionBatchRequest.from_contract(
        CallableContract.from_callable(export_to_spreadsheet),
        artifact_batch=batch,
        kwargs=kwargs,
        runtime_context=None,
        map_partition_invocations=map_partitions,
    )
    actual = {
        path: (
            output.rendered() if isinstance(output, ColumnarCsvOutput) else output
        ).require_text_content()
        for path, output in _partitioned_spreadsheet_export(request).items()
    }
    assert actual == expected
    assert [
        (
            invocation.artifact_batch.input_specs[0].name,
            next(iter(invocation.artifact_batch.records_by_axis)),
        )
        for invocation in mapped[2:]
    ] == (
        []
        if overlapping_declarations
        else [
            ("parents", "W001"),
            ("parents", "W002"),
            ("children", "W001"),
            ("children", "W002"),
        ]
    )
    assert len(mapped) == (0 if overlapping_declarations else 6)


@pytest.mark.parametrize("nan_representation", tuple(SpreadsheetNanRepresentation))
@pytest.mark.parametrize("sequence_columns", (False, True))
def test_rendered_partitions_keep_sparse_csv_without_raw_value_transport(
    nan_representation,
    sequence_columns,
):
    import pickle
    import numpy as np
    from openhcs.processing.materialization.core import (
        ColumnarCsvOutput,
        RenderedColumnarCsvOutput,
    )
    from openhcs.processing.backends.cellprofiler.spreadsheet_export import (
        CellProfilerSpreadsheetCsvOptions,
    )

    options = CellProfilerSpreadsheetCsvOptions(
        selection=SpreadsheetFileSelection(("Image",), "Image.csv"),
        active_subjects=("Image",),
        delimiter=SpreadsheetDelimiter.COMMA,
        nan_representation=nan_representation,
    )
    sources = (
        {
            "image_number": np.array([1, 1]),
            "quoted\nfield": np.array([MEASUREMENT_SPARSE_CELL, None], object),
            "a": np.array(["x,y", "x\ny"], object),
        },
        {
            "image_number": np.array([2, 2]),
            "quoted\nfield": np.array([np.nan, ""], object),
            "a": np.array(['"', ""], object),
            "extra": np.array([np.inf, "q"], object),
        },
    )
    if sequence_columns:
        sources = tuple(
            {name: list(values) for name, values in columns.items()}
            for columns in sources
        )
    outputs = tuple(
        ColumnarCsvOutput(
            path="Image.csv",
            options=options,
            content=MeasurementSparseColumnarRows(
                columns,
                fields=tuple(FieldSpec(name, required=False) for name in columns),
            ),
        )
        for columns in sources
    )
    expected = (
        ColumnarCsvOutput.compose(outputs, partition_fields=("image_number",))
        .rendered()
        .content
    )
    realized = tuple(
        output.realized_for_composition(partition_fields=("image_number",))
        for output in outputs
    )
    transported = tuple(pickle.loads(pickle.dumps(output)) for output in realized)
    assert all(tuple(output.key_columns) == ("image_number",) for output in transported)
    assert all(not output._decoded_columns for output in transported)
    result = RenderedColumnarCsvOutput.compose(
        transported, partition_fields=("image_number",)
    )
    assert result.content == expected
    assert result.table_shape()[1] == 4
    with pytest.raises(ValueError, match="overlap"):
        RenderedColumnarCsvOutput.compose(
            (realized[0], realized[0]), partition_fields=("image_number",)
        )
    sources[0]["image_number"][:] = [99, 99]
    assert realized[0].key_columns["image_number"].tolist() == [1, 1]


def test_rendered_matching_headers_compose_without_decoding_value_columns():
    import numpy as np
    from openhcs.processing.materialization.core import (
        ColumnarCsvOutput,
        RenderedColumnarCsvOutput,
    )
    from openhcs.processing.backends.cellprofiler.spreadsheet_export import (
        CellProfilerSpreadsheetCsvOptions,
    )

    options = CellProfilerSpreadsheetCsvOptions(
        selection=SpreadsheetFileSelection(("Image",), "Image.csv"),
        active_subjects=("Image",),
        delimiter=SpreadsheetDelimiter.COMMA,
        nan_representation=SpreadsheetNanRepresentation.NULL,
    )
    outputs = tuple(
        ColumnarCsvOutput(
            path="Image.csv",
            options=options,
            content=MeasurementSparseColumnarRows(
                {"image_number": np.array([number]), "value": np.array([number + 0.5])},
                fields=(FieldSpec("image_number"), FieldSpec("value")),
            ),
        ).realized_for_composition(partition_fields=("image_number",))
        for number in (1, 2)
    )
    result = RenderedColumnarCsvOutput.compose(
        outputs, partition_fields=("image_number",)
    )
    assert result.content == b"image_number,value\n1,1.5\n2,2.5\n"
    assert not result._decoded_columns
    assert all(not output._decoded_columns for output in outputs)
    assert result.table_shape() == (("image_number", "value"), 2)


def test_csv_writer_shape_preserves_contextual_headers_and_empty_dialects():
    from openhcs.processing.materialization.core import ColumnarCsvOutput
    from openhcs.processing.materialization.options import CsvOptions
    from openhcs.processing.backends.cellprofiler.spreadsheet_export import (
        CellProfilerSpreadsheetCsvOptions,
    )

    def cp_options(subjects):
        return CellProfilerSpreadsheetCsvOptions(
            selection=SpreadsheetFileSelection(subjects, "out.csv"),
            active_subjects=subjects,
            delimiter=SpreadsheetDelimiter.COMMA,
            nan_representation=SpreadsheetNanRepresentation.NULL,
        )

    rows = MeasurementSparseColumnarRows(
        {"image_number": [1], "Cells_value": [2], "Nuclei_value": [3]},
        fields=(
            FieldSpec("image_number"),
            FieldSpec("Cells_value"),
            FieldSpec("Nuclei_value"),
        ),
    )
    output = ColumnarCsvOutput(
        path="out.csv", content=rows, options=cp_options(("Cells", "Nuclei"))
    )
    assert output.table_shape() == (("Image", "Cells", "Nuclei"), 2)
    assert output.rendered().table_shape() == output.table_shape()
    assert (
        output.realized_for_composition(
            partition_fields=("image_number",)
        ).table_shape()
        == output.table_shape()
    )
    empty = MeasurementSparseColumnarRows({}, fields=())
    cp_empty = ColumnarCsvOutput(
        path="empty.csv", content=empty, options=cp_options(("Image",))
    )
    assert cp_empty.rendered().content == b""
    assert cp_empty.table_shape() == ((), 0)
    generic_empty = ColumnarCsvOutput(
        path="empty.csv", content=empty, options=CsvOptions()
    )
    assert generic_empty.rendered().content == b"\r\n"
    assert generic_empty.table_shape() == ((), 0)
    # The nominal field owner rejects empty names; the generic mapping writer
    # still preserves the one-column blank CSV grammar.
    from openhcs.processing.materialization.core import _render_csv_rows

    with pytest.raises(ValueError, match="cannot be empty"):
        FieldSpec("")
    assert _render_csv_rows(({"": ""},), ("",)) == '""\r\n""\r\n'


def test_rendered_fixed_fields_snapshot_mutable_cells_and_keep_unrendered_identity():
    import numpy as np
    from openhcs.processing.materialization.core import (
        ColumnarCsvOutput,
        RenderedColumnarCsvOutput,
    )
    from openhcs.processing.backends.cellprofiler.spreadsheet_export import (
        CellProfilerSpreadsheetCsvOptions,
    )

    options = CellProfilerSpreadsheetCsvOptions(
        selection=SpreadsheetFileSelection(("Image",), "Image.csv"),
        active_subjects=("Image",),
        delimiter=SpreadsheetDelimiter.COMMA,
        nan_representation=SpreadsheetNanRepresentation.NULL,
        fields=("value",),
    )
    mutable = [3, 4]
    values = np.empty(1, object)
    values[0] = mutable
    source = ColumnarCsvOutput(
        path="Image.csv",
        options=options,
        content=MeasurementSparseColumnarRows(
            {"image_number": [1], "value": values, "excluded": [5]},
            fields=(
                FieldSpec("image_number"),
                FieldSpec("value"),
                FieldSpec("excluded"),
            ),
        ),
    )
    rendered = source.realized_for_composition(partition_fields=("image_number",))
    expected = source.rendered().content
    mutable.append(6)
    assert rendered.content == expected
    assert "excluded" not in rendered.columns
    assert rendered.key_columns["image_number"].tolist() == [1]
    assert (
        RenderedColumnarCsvOutput.compose(
            (rendered,), partition_fields=("image_number",)
        ).content
        == expected
    )


@pytest.mark.parametrize("nan_representation", tuple(SpreadsheetNanRepresentation))
def test_compact_csv_fallback_preserves_physical_dtype_promotion(nan_representation):
    import pickle
    import numpy as np
    from openhcs.processing.materialization.core import (
        ColumnarCsvOutput,
        RenderedColumnarCsvOutput,
    )
    from openhcs.processing.backends.cellprofiler.spreadsheet_export import (
        CellProfilerSpreadsheetCsvOptions,
    )

    options = CellProfilerSpreadsheetCsvOptions(
        selection=SpreadsheetFileSelection(("Image",), "Image.csv"),
        active_subjects=("Image",),
        delimiter=SpreadsheetDelimiter.COMMA,
        nan_representation=nan_representation,
    )
    pairs = (
        (np.array([1.1], np.float32), np.array([1.1], np.float64)),
        (np.array([False, True]), np.array([2, 3])),
        (np.array([np.nan, np.inf, -np.inf]), np.array([1j, 2j, 3j])),
        (np.array([np.nan, np.inf, -np.inf]), np.array(["x", "y", "z"])),
        (np.array([b"a", b"b"]), np.array(["x", "y"])),
        (
            np.array(["2000-01-01"], dtype="datetime64[D]"),
            np.array(["2000-01-02T01:02"], dtype="datetime64[m]"),
        ),
        (np.array([2**63 - 1], np.int64), np.array([1.1], np.float64)),
        (np.array([np.longdouble("1e4000")]), np.array([1.1])),
        (np.array([1.1], np.float32), np.array([None], object)),
    )
    for left, right in pairs:
        sources = tuple(
            ColumnarCsvOutput(
                path="Image.csv",
                options=options,
                content=MeasurementSparseColumnarRows(
                    columns,
                    fields=tuple(
                        FieldSpec(
                            name, float if name == "value" else None, required=False
                        )
                        for name in columns
                    ),
                ),
            )
            for columns in (
                {"image_number": np.full(len(left), 1), "value": left},
                {
                    "image_number": np.full(len(right), 2),
                    "value": right,
                    "extra": np.ones(len(right)),
                },
            )
        )
        expected = (
            ColumnarCsvOutput.compose(sources, partition_fields=("image_number",))
            .rendered()
            .content
        )
        rendered = tuple(
            pickle.loads(
                pickle.dumps(
                    source.realized_for_composition(partition_fields=("image_number",))
                )
            )
            for source in sources
        )
        if "value" in rendered[0].raw_columns:
            left[:] = np.zeros_like(left)
        actual = RenderedColumnarCsvOutput.compose(
            rendered, partition_fields=("image_number",)
        )
        assert actual.content == expected, (
            left.dtype,
            right.dtype,
            actual.content,
            expected,
        )
        assert all(
            not values.flags.writeable
            for output in rendered
            for values in output.raw_columns.values()
        )
        for output in rendered:
            assert all(
                len(bits) == (2 * output.data_row_count + 7) // 8
                for bits in output.nonfinite_codes.values()
            )


def test_compact_csv_nested_fast_compose_keeps_original_dtype_segments():
    import numpy as np
    from openhcs.processing.materialization.core import (
        ColumnarCsvOutput,
        RenderedColumnarCsvOutput,
    )
    from openhcs.processing.backends.cellprofiler.spreadsheet_export import (
        CellProfilerSpreadsheetCsvOptions,
    )

    options = CellProfilerSpreadsheetCsvOptions(
        selection=SpreadsheetFileSelection(("Image",), "Image.csv"),
        active_subjects=("Image",),
        delimiter=SpreadsheetDelimiter.COMMA,
        nan_representation=SpreadsheetNanRepresentation.NULL,
    )
    sources = tuple(
        ColumnarCsvOutput(
            path="Image.csv",
            options=options,
            content=MeasurementSparseColumnarRows(
                columns,
                fields=tuple(FieldSpec(name, required=False) for name in columns),
            ),
        )
        for columns in (
            {
                "image_number": np.array([1, 1]),
                "value": np.array([1.1, np.inf], np.float32),
            },
            {
                "image_number": np.array([2, 2]),
                "value": np.array([1.1, -np.inf], np.float64),
            },
            {
                "image_number": np.array([3]),
                "value": np.array([1j]),
                "extra": np.array([5]),
            },
        )
    )
    rendered = tuple(
        source.realized_for_composition(partition_fields=("image_number",))
        for source in sources
    )
    first = RenderedColumnarCsvOutput.compose(
        rendered[:2], partition_fields=("image_number",)
    )
    assert not first._decoded_columns
    result = RenderedColumnarCsvOutput.compose(
        (first, rendered[2]), partition_fields=("image_number",)
    )
    expected = (
        ColumnarCsvOutput.compose(sources, partition_fields=("image_number",))
        .rendered()
        .content
    )
    assert result.content == expected


def test_compact_csv_preserves_original_semantic_schema_conflicts():
    import numpy as np
    from openhcs.processing.materialization.core import (
        ColumnarCsvOutput,
        RenderedColumnarCsvOutput,
    )
    from openhcs.processing.materialization.options import CsvOptions

    outputs = tuple(
        ColumnarCsvOutput(
            path="out.csv",
            options=CsvOptions(),
            content=MeasurementSparseColumnarRows(
                {"image_number": np.array([number]), "value": np.array([1.1])},
                fields=(FieldSpec("image_number"), FieldSpec("value", declared)),
            ),
        ).realized_for_composition(partition_fields=("image_number",))
        for number, declared in ((1, float), (2, str))
    )
    with pytest.raises(ValueError, match="Conflicting"):
        RenderedColumnarCsvOutput.compose(outputs, partition_fields=("image_number",))


def test_compact_csv_requested_absent_field_uses_original_merged_declaration():
    import numpy as np
    from openhcs.processing.materialization.core import (
        ColumnarCsvOutput,
        RenderedColumnarCsvOutput,
    )
    from openhcs.processing.backends.cellprofiler.spreadsheet_export import (
        CellProfilerSpreadsheetCsvOptions,
    )

    options = CellProfilerSpreadsheetCsvOptions(
        selection=SpreadsheetFileSelection(("Image",), "Image.csv"),
        active_subjects=("Image",),
        delimiter=SpreadsheetDelimiter.COMMA,
        nan_representation=SpreadsheetNanRepresentation.NULL,
        fields=("image_number", "value"),
    )
    sources = (
        ColumnarCsvOutput(
            path="Image.csv",
            options=options,
            content=MeasurementSparseColumnarRows(
                {"image_number": np.array([1])},
                fields=(FieldSpec("image_number"),),
            ),
        ),
        ColumnarCsvOutput(
            path="Image.csv",
            options=options,
            content=MeasurementSparseColumnarRows(
                {"image_number": np.array([2]), "value": np.array([1.1], np.float32)},
                fields=(FieldSpec("image_number"), FieldSpec("value", float)),
            ),
        ),
    )
    expected = (
        ColumnarCsvOutput.compose(sources, partition_fields=("image_number",))
        .rendered()
        .content
    )
    result = RenderedColumnarCsvOutput.compose(
        tuple(
            source.realized_for_composition(partition_fields=("image_number",))
            for source in sources
        ),
        partition_fields=("image_number",),
    )
    assert result.content == expected
    assert result.source.content.fields[1] == FieldSpec("value", float)
