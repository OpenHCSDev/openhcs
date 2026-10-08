from __future__ import annotations

from base64 import b64decode
from dataclasses import replace
from io import BytesIO
from pathlib import Path
import sqlite3
from types import MappingProxyType, SimpleNamespace

import numpy as np
import pytest
from PIL import Image

from openhcs.constants.constants import AllComponents
from openhcs.core.artifacts import (
    ObjectLabelsArtifactType,
    ArtifactOutputPlan,
    ArtifactSpec,
    ArtifactSpecCollection,
    ImageArtifactType,
    MeasurementsArtifactType,
    RelationshipsArtifactType,
    SpecialArtifactType,
)
from openhcs.core.callable_contract import CallableContract, FunctionStepExecutionScope
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.function_patterns import (
    FunctionInvocationKey,
    compile_function_pattern,
)
from openhcs.core.invocation_artifacts import ArtifactDeclarationStepContext
from openhcs.core.pipeline.artifact_planning import artifact_producers_for_outputs
from openhcs.core.measurement_row_materialization import (
    MeasurementProjectedColumnarRows,
    MeasurementSparseColumnarRows,
)
from openhcs.core.runtime_measurements import MeasurementScope, MeasurementSubject
from openhcs.core.runtime_relationships import (
    DirectedObjectRelationshipPayload,
    ObjectRelationshipDeclaration,
)
from openhcs.core.runtime_tabular_values import FieldSpec
from openhcs.core.runtime_stores import RuntimeArtifactBatch, RuntimeValueStore
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_measurements import (
    MeasurementTable,
)
from openhcs.core.runtime_relationships import (
    ObjectRelationship,
)
from openhcs.core.runtime_measurements import (
    MeasurementRowAxisField,
    MeasurementRowValueField,
)
from openhcs.core.source_bindings import (
    CompiledSourceBindingPlan,
    NamedSourceBinding,
    SourceProjectionRole,
    StepSourceBindingsConfig,
)
from openhcs.core.source_matching import SourceImageSetIdentityPolicy
from openhcs.core.source_matching import with_original_source_metadata
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_image_provenance import (
    RuntimeSourceImageProvenancePlane,
    SourceImageIdentity,
    SourceImageProvenanceContributor,
)
from openhcs.core.source_projection import (
    OpenHCSPlaneAddress,
    SourceArtifactProjection,
    SourcePlaneProjection,
    SourceProjectionMetadataSerializer,
    SourceProjectionSet,
)
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser
from polystore.virtual_workspace import SourcePixelRef
from openhcs.interop.cellprofiler.analyst_export import (
    CPAImageChannelSpec,
    CPAPropertiesRenderer,
    CPASQLiteRenderer,
    CPATableRowProjection,
    CellProfilerAnalystProjectionBuilder,
    CellProfilerDatabaseExportSettings,
    CellProfilerObjectTableMode,
)
from openhcs.interop.cellprofiler.database_column_dialect import (
    CellProfilerDatabaseColumnDialect,
    CellProfilerProjectedTable,
)
from openhcs.interop.cellprofiler.image_set_numbering import (
    CellProfilerImageSetNumbering,
)
from openhcs.interop.cellprofiler.parser import ModuleBlock, ModuleSetting
from openhcs.interop.cellprofiler.settings_binder import SettingsBinder
from openhcs.processing.backends.cellprofiler.export_to_database import (
    ExportToDatabaseModule,
    export_to_database,
)
from openhcs.processing.materialization import FileBundleOptions
from openhcs.core.runtime_artifact_values import RuntimeValue

AXIS_ID = "A01_s1"
RUNTIME_IMAGE_FIELD = MeasurementRowAxisField.SLICE_INDEX.value


def _projection_builder() -> CellProfilerAnalystProjectionBuilder:
    return CellProfilerAnalystProjectionBuilder(
        source_binding_plan=CompiledSourceBindingPlan.empty()
    )


def _projection_builder_for_fields(
    metadata_fields: tuple[FieldSpec, ...],
) -> CellProfilerAnalystProjectionBuilder:
    return CellProfilerAnalystProjectionBuilder(
        source_binding_plan=CompiledSourceBindingPlan(
            metadata_fields=metadata_fields,
        )
    )


def test_cpa_row_projection_derives_fields_once_per_table_subject(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    projection = CPATableRowProjection(
        CellProfilerDatabaseColumnDialect(),
        CellProfilerImageSetNumbering(SourceImageSetIdentityPolicy()),
    )
    subject = MeasurementSubject(MeasurementScope.EXPERIMENT)
    calls: list[tuple[str, MeasurementSubject, str]] = []
    original = CPATableRowProjection._project_measurement_field

    def count_projection(
        self: CPATableRowProjection,
        table: MeasurementTable,
        field_name: str,
        *,
        subject: MeasurementSubject,
        project_database_field,
    ) -> FieldSpec | None:
        calls.append((table.name, subject, field_name))
        return original(
            self, table, field_name, subject=subject,
            project_database_field=project_database_field,
        )

    monkeypatch.setattr(
        CPATableRowProjection,
        "_project_measurement_field",
        count_projection,
    )
    first = MeasurementTable(
        name="FirstExperiment",
        rows=MeasurementProjectedColumnarRows(
            {"Count_Nuclei": (1, 2, 3)},
            fields=(FieldSpec("Count_Nuclei", int),),
        ),
        subject=subject,
    )
    second = MeasurementTable(
        name="SecondExperiment",
        rows=MeasurementProjectedColumnarRows(
            {"Count_Nuclei": (4.5, 5.5)},
            fields=(FieldSpec("Count_Nuclei", float),),
        ),
        subject=subject,
    )

    first_subject, first_rows, first_fields = next(projection.measurement_projections(first, scope=None))
    assert first_subject == subject
    assert first_fields == (FieldSpec("Count_Nuclei", int),)
    assert first_rows.row_mappings() == (
        {"Count_Nuclei": 1},
        {"Count_Nuclei": 2},
        {"Count_Nuclei": 3},
    )
    second_subject, second_rows, second_fields = next(projection.measurement_projections(second, scope=None))
    assert second_subject == subject
    assert second_fields == (FieldSpec("Count_Nuclei", float),)
    assert second_rows.row_mappings() == (
        {"Count_Nuclei": 4.5},
        {"Count_Nuclei": 5.5},
    )
    object_table = MeasurementTable(
        name="ObjectMeasurements",
        rows=MeasurementProjectedColumnarRows(
            {"AreaShape_Area": (1.0,)},
            fields=(FieldSpec("AreaShape_Area", float),),
        ),
        subject=MeasurementSubject(MeasurementScope.OBJECT, "Cells"),
    )
    cells = MeasurementSubject(MeasurementScope.OBJECT, "Cells")
    nuclei = MeasurementSubject(MeasurementScope.OBJECT, "Nuclei")
    object_field_cache: dict[tuple[MeasurementSubject, str], FieldSpec | None] = {}
    assert projection._project_runtime_rows(
        object_table,
        object_table.rows,
        subject=cells,
        field_projection_cache=object_field_cache,
        project_database_field=None,
    ).row_mappings()[0] == {"Cells_AreaShape_Area": 1.0}
    assert projection._project_runtime_rows(
        object_table,
        MeasurementProjectedColumnarRows({"AreaShape_Area": (2.0,)}, fields=(FieldSpec("AreaShape_Area", float),)),
        subject=nuclei,
        field_projection_cache=object_field_cache,
        project_database_field=None,
    ).row_mappings()[0] == {"Nuclei_AreaShape_Area": 2.0}
    assert calls == [
        ("FirstExperiment", subject, "Count_Nuclei"),
        ("SecondExperiment", subject, "Count_Nuclei"),
        ("ObjectMeasurements", cells, "AreaShape_Area"),
        ("ObjectMeasurements", nuclei, "AreaShape_Area"),
    ]


def test_database_field_projection_refreshes_declarations_and_live_dtype_hooks(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from openhcs.processing.backends.cellprofiler.relationships import (
        RelateObjectsModule,
    )

    field = FieldSpec("Distance_Centroid_Nuclei", float, required=False)
    project_field = RelateObjectsModule.database_measurement_field_projection()
    assert project_field(field) == replace(field, dtype=int)
    monkeypatch.setattr(
        RelateObjectsModule.DistanceMeasurementFeature,
        "database_measurement_dtype",
        classmethod(lambda cls: float),
    )
    assert project_field(field) == field
    monkeypatch.undo()
    monkeypatch.setattr(RelateObjectsModule, "DistanceMeasurementFeature", None)
    assert RelateObjectsModule.database_measurement_field(field) == field
    assert project_field(field) == replace(field, dtype=int)

    projection = CPATableRowProjection(
        CellProfilerDatabaseColumnDialect(),
        CellProfilerImageSetNumbering(SourceImageSetIdentityPolicy()),
    )
    table = MeasurementTable(
        name="EmptyDistances",
        rows=MeasurementProjectedColumnarRows(
            {field.name: ()}, fields=(field,),
        ),
        subject=MeasurementSubject(MeasurementScope.EXPERIMENT),
        measurement_feature_owner=RelateObjectsModule,
    )
    _subject, actual_rows, actual_fields = next(projection.measurement_projections(table, scope=None))
    assert actual_rows.row_mappings() == ()
    assert actual_fields == (field,)
    monkeypatch.undo()
    _subject, actual_rows, actual_fields = next(projection.measurement_projections(table, scope=None))
    assert actual_rows.row_mappings() == ()
    assert actual_fields == (replace(field, dtype=int),)

    class CustomFieldOwner(RelateObjectsModule):
        module_name = None

        @classmethod
        def database_measurement_field_projection(cls):
            return lambda source_field: replace(source_field, dtype=str)

    custom_table = replace(table, measurement_feature_owner=CustomFieldOwner)
    _subject, actual_rows, actual_fields = next(projection.measurement_projections(custom_table, scope=None))
    assert actual_rows.row_mappings() == ()
    assert actual_fields == (replace(field, dtype=str),)
    assert CustomFieldOwner.database_measurement_field(field).dtype is str


def test_cpa_alias_collision_precedes_later_module_field_matching(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from openhcs.processing.backends.cellprofiler.relationships import (
        RelateObjectsModule,
    )

    def reject_later_matching(self, feature_name: str) -> bool:
        raise AssertionError("Later module field matching must not run.")

    monkeypatch.setattr(
        RelateObjectsModule.DistanceMeasurementFeature,
        "matches_feature_name",
        reject_later_matching,
    )
    table = MeasurementTable(
        name="AliasCollision",
        rows=MeasurementProjectedColumnarRows(
            {
                "slice_index": (0,),
                "image_id": (0,),
                "Distance_Centroid_Nuclei": (1.0,),
            },
            fields=(
                FieldSpec("slice_index", int),
                FieldSpec("image_id", int),
                FieldSpec("Distance_Centroid_Nuclei", float),
            ),
        ),
        subject=MeasurementSubject(MeasurementScope.EXPERIMENT),
        measurement_feature_owner=RelateObjectsModule,
    )
    projection = CPATableRowProjection(
        CellProfilerDatabaseColumnDialect(),
        CellProfilerImageSetNumbering(SourceImageSetIdentityPolicy()),
    )
    with pytest.raises(ValueError, match="overwrite field 'ImageNumber'"):
        next(projection.measurement_projections(table, scope=None))


def test_default_cpa_channels_follow_compiled_source_binding_order() -> None:
    source_blue = ArtifactSpec.output("OrigBlue", ImageArtifactType)
    source_green = ArtifactSpec.output("OrigGreen", ImageArtifactType)
    derived_blue = ArtifactSpec.output("IllumBlue", ImageArtifactType)
    channels = CPAImageChannelSpec.defaults_for_artifacts(
        (derived_blue, source_green, source_blue),
        source_binding_plan=CompiledSourceBindingPlan(
            bindings=(
                NamedSourceBinding(alias=source_blue.name),
                NamedSourceBinding(alias=source_green.name),
            )
        ),
    )

    assert tuple(channel.alias for channel in channels) == (
        "OrigBlue",
        "OrigGreen",
        "IllumBlue",
    )


class _MetadataHandlerStub:
    def source_workspace_metadata_document(self, _plate_path):
        return None


def _export_context() -> ProcessingContext:
    context = ProcessingContext(
        step_plans={
            0: CompiledStepPlan(
                step_index=0,
                step_name="ExportToDatabase",
                step_type="FunctionStep",
                axis_id=AXIS_ID,
                source_binding_plan=CompiledSourceBindingPlan.empty(),
                compiled_function_pattern=compile_function_pattern(
                    export_to_database,
                    {},
                    {},
                ),
            )
        },
        filemanager=SimpleNamespace(exists=lambda *_args: False),
    )
    context.plate_path = Path("/")
    context.microscope_handler = SimpleNamespace(
        metadata_handler=_MetadataHandlerStub(),
        source_admission_config=lambda: None,
    )
    return context


def test_projected_table_rejects_duplicate_conflicting_and_undeclared_fields() -> None:
    with pytest.raises(ValueError, match="duplicate fields"):
        CellProfilerProjectedTable(
            "Per_Image",
            (),
            (FieldSpec("ImageNumber", int), FieldSpec("ImageNumber", int)),
        )
    with pytest.raises(ValueError, match="Conflicting"):
        CellProfilerProjectedTable(
            "Per_Image",
            (),
            (FieldSpec("Value", int), FieldSpec("Value", float)),
        )
    with pytest.raises(ValueError, match="undeclared fields"):
        CellProfilerProjectedTable(
            "Per_Image",
            ({"Other": 1},),
            (FieldSpec("Value", int),),
        )


def test_projection_uses_only_exact_batch_records_and_merges_subject_rows() -> None:
    store = RuntimeValueStore()
    image_measurements = _record_measurements(
        store,
        table=MeasurementTable(
            name="ImageMeasurements",
            rows=MeasurementSparseColumnarRows.from_rows(
                ({RUNTIME_IMAGE_FIELD: 0, "Count_Nuclei": 2},),
                fields=(
                    FieldSpec(RUNTIME_IMAGE_FIELD, int),
                    FieldSpec("Count_Nuclei", int),
                ),
            ),
            subject=MeasurementSubject(MeasurementScope.IMAGE, "Image"),
        ),
    )
    nuclei_shape = _record_measurements(
        store,
        table=MeasurementTable(
            name="NucleiShape",
            rows=MeasurementProjectedColumnarRows(
                {
                    RUNTIME_IMAGE_FIELD: (0, 0),
                    "ObjectNumber": (1, 2),
                    "AreaShape_Area": (24.0, 36.0),
                },
                fields=(
                    FieldSpec(RUNTIME_IMAGE_FIELD, int),
                    FieldSpec("ObjectNumber", int),
                    FieldSpec("AreaShape_Area", float),
                ),
            ),
            subject=MeasurementSubject(
                MeasurementScope.OBJECT, "Nuclei", "ObjectNumber"
            ),
        ),
    )
    nuclei_intensity = _record_measurements(
        store,
        table=MeasurementTable(
            name="NucleiIntensity",
            rows=MeasurementProjectedColumnarRows(
                {
                    RUNTIME_IMAGE_FIELD: (0, 0),
                    "ObjectNumber": (1, 2),
                    "Intensity_Mean": (0.2, 0.4),
                },
                fields=(
                    FieldSpec(RUNTIME_IMAGE_FIELD, int),
                    FieldSpec("ObjectNumber", int),
                    FieldSpec("Intensity_Mean", float),
                ),
            ),
            subject=MeasurementSubject(
                MeasurementScope.OBJECT, "Nuclei", "ObjectNumber"
            ),
        ),
    )
    relationship = _record_relationship(
        store,
        relationship=ObjectRelationship(
            name="Cells_Nuclei_relationships",
            source_component_metadata=MappingProxyType({"well": "A01"}),
            declaration=ObjectRelationshipDeclaration(
                source=ArtifactSpec.output("Cells", ObjectLabelsArtifactType).ref(),
                target=ArtifactSpec.output("Nuclei", ObjectLabelsArtifactType).ref(),
                relationship_type="parent_child",
                source_role="parent",
                target_role="child",
                source_id_field="parent_id",
                target_id_field="child_id",
                producer_module_number=1,
                source_runtime_slice_offset=0,
                target_runtime_slice_offset=0,
            ),
            payload=DirectedObjectRelationshipPayload(
                source_ids=(10, 10),
                target_ids=(1, 2),
                slice_indices=(),
                slice_count=None,
            ),
        ),
    )
    undeclared = _record_measurements(
        store,
        table=MeasurementTable(
            name="Undeclared",
            rows=MeasurementSparseColumnarRows.from_rows(
                ({RUNTIME_IMAGE_FIELD: 98, "Count_Nuclei": 999},),
                fields=(
                    FieldSpec(RUNTIME_IMAGE_FIELD, int),
                    FieldSpec("Count_Nuclei", int),
                ),
            ),
            subject=MeasurementSubject(MeasurementScope.IMAGE, "Image"),
        ),
    )
    del undeclared

    image_spec = ArtifactSpec.input("DNA", ImageArtifactType)
    batch = RuntimeArtifactBatch(
        input_specs=(
            image_spec,
            image_measurements,
            nuclei_shape,
            nuclei_intensity,
            relationship,
        ),
        records_by_axis={AXIS_ID: store.values()},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )
    settings = _settings()
    channels = CPAImageChannelSpec.defaults_for_artifacts(
        (image_spec,),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
    )

    projection = _projection_builder().build(
        batch,
        settings,
        channels,
    )

    assert projection.image_table.table_name == "CPA_Per_Image"
    image_rows = _external_rows(projection.image_table)
    assert tuple(row["ImageNumber"] for row in image_rows) == (1,)
    assert image_rows[0]["Image_Count_Nuclei"] == 2
    assert all(
        isinstance(field_name, str) for field_name in projection.image_table.rows[0]
    )
    assert projection.image_table.subject == MeasurementSubject(
        MeasurementScope.IMAGE,
        "Image",
    )
    assert len(projection.object_tables) == 1
    assert projection.object_tables[0].table_name == "CPA_Per_Nuclei"
    assert _field_rows(projection.object_tables[0]) == (
        {
            "ImageNumber": 1,
            "Nuclei_Number_Object_Number": 1,
            "Nuclei_AreaShape_Area": 24.0,
            "Nuclei_Intensity_Mean": 0.2,
        },
        {
            "ImageNumber": 1,
            "Nuclei_Number_Object_Number": 2,
            "Nuclei_AreaShape_Area": 36.0,
            "Nuclei_Intensity_Mean": 0.4,
        },
    )
    assert projection.relationship_tables[0].table_name == (
        "CPA_Cells_Nuclei_relationships"
    )
    assert all(
        "source_component_metadata" not in row
        for row in projection.relationship_tables[0].rows
    )
    sqlite_bytes = CPASQLiteRenderer().render(projection, settings)
    assert sqlite_bytes.startswith(b"SQLite format 3\x00")

    # Exercise the mapped parent consume boundary with disjoint image domains,
    # correlated object measurements and relationship endpoints together.
    second_axis = "second-well"
    second_records = tuple(
        replace(
            record,
            key=replace(
                record.key, scope=replace(record.key.scope, axis_id=second_axis)
            ),
        )
        for record in store.values()
    )
    two_axes = replace(
        batch, records_by_axis={AXIS_ID: store.values(), second_axis: second_records}
    )
    partitions = []

    def map_projections(func, invocations):
        partitions.append(len(invocations))
        assert all(invocation[0].context is None for invocation in invocations)
        return tuple(func(invocation) for invocation in invocations)

    serial = _projection_builder().build(two_axes, settings, channels)
    mapped = _projection_builder().build(
        two_axes, settings, channels, map_partition_invocations=map_projections
    )
    assert partitions == [2]
    assert CPASQLiteRenderer().render(mapped, settings) == CPASQLiteRenderer().render(
        serial, settings
    )


def test_long_measurement_schema_remains_owned_by_each_projected_subject() -> None:
    store = RuntimeValueStore()
    measurements = _record_measurements(
        store,
        table=MeasurementTable(
            name="MixedSubjects",
            rows=MeasurementSparseColumnarRows.from_rows(
                (
                    {
                        RUNTIME_IMAGE_FIELD: 0,
                        "object_name": "Child",
                        "object_label": 1,
                        "feature_name": "Location_Center_X",
                        "result_value": 2.0,
                    },
                    {
                        RUNTIME_IMAGE_FIELD: 0,
                        "object_name": "Parent",
                        "object_label": 1,
                        "feature_name": "Mean_Child_Area",
                        "result_value": 3.0,
                    },
                ),
                fields=(
                    FieldSpec(RUNTIME_IMAGE_FIELD, int),
                    FieldSpec("object_name", str),
                    FieldSpec("object_label", int),
                    FieldSpec("feature_name", str),
                    FieldSpec("result_value", float),
                    FieldSpec("Location_Center_X", float, required=False),
                    FieldSpec("Mean_Child_Area", float, required=False),
                ),
            ),
            subject=MeasurementSubject(MeasurementScope.IMAGE, "image"),
        ),
    )
    batch = RuntimeArtifactBatch(
        input_specs=(measurements,),
        records_by_axis={AXIS_ID: store.values()},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    projection = _projection_builder().build(batch, _settings(), ())

    fields_by_subject = {
        table.subject.object_name: {field.name for field in table.columns}
        for table in projection.object_tables
        if table.subject is not None
    }
    assert fields_by_subject["Child"] == {
        "ImageNumber",
        "Child_Number_Object_Number",
        "Child_Location_Center_X",
    }
    assert fields_by_subject["Parent"] == {
        "ImageNumber",
        "Parent_Number_Object_Number",
        "Parent_Mean_Child_Area",
    }


def test_projection_adds_common_typed_source_provenance_to_image_rows() -> None:
    store = RuntimeValueStore()
    measurements = _record_measurements(
        store,
        table=MeasurementTable(
            name="ImageMeasurements",
            rows=MeasurementSparseColumnarRows.from_rows(
                ({RUNTIME_IMAGE_FIELD: 0, "Count_Nuclei": 2},),
                fields=(
                    FieldSpec(RUNTIME_IMAGE_FIELD, int),
                    FieldSpec("Count_Nuclei", int),
                ),
            ),
            subject=MeasurementSubject(MeasurementScope.IMAGE, "Image"),
        ),
    )
    dna = _record_image(
        store,
        name="DNA",
        source_path="/images/A01/dna.tif",
        metadata={
            "Plate": "20585",
            "Well": "A01",
            "Site": "1",
            "ChannelNumber": "1",
        },
    )
    rna = _record_image(
        store,
        name="RNA",
        source_path="/images/A01/rna.tif",
        metadata={
            "Plate": "20585",
            "Well": "A01",
            "Site": "1",
            "ChannelNumber": "2",
        },
    )
    batch = RuntimeArtifactBatch(
        input_specs=(dna, rna, measurements),
        records_by_axis={AXIS_ID: store.values()},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(
            frozenset((AllComponents.CHANNEL,))
        ),
    )

    projection = _projection_builder_for_fields(
        (
            FieldSpec("Plate", str, required=False),
            FieldSpec("Well", str, required=False),
            FieldSpec("Site", int, required=False),
            FieldSpec("ChannelNumber", int, required=False),
            FieldSpec("FileLocation", str, required=False),
            FieldSpec("Frame", int, required=False),
            FieldSpec("Series", int, required=False),
        )
    ).build(
        batch,
        _settings(),
        CPAImageChannelSpec.defaults_for_artifacts(
            (dna, rna),
            source_binding_plan=CompiledSourceBindingPlan.empty(),
        ),
    )

    assert _external_rows(projection.image_table)[0] == {
        "ImageNumber": 1,
        "Image_Count_Nuclei": 2,
        "Image_PathName_DNA": "/images/A01",
        "Image_FileName_DNA": "dna.tif",
        "Image_PathName_RNA": "/images/A01",
        "Image_FileName_RNA": "rna.tif",
        "Image_Metadata_Plate": "20585",
        "Image_Metadata_Well": "A01",
        "Image_Metadata_Site": 1,
        "Image_Metadata_ChannelNumber": None,
        "Image_Metadata_FileLocation": None,
        "Image_Metadata_Frame": 0,
        "Image_Metadata_Series": 0,
        "Image_Group_Index": 1,
        "Image_Group_Length": 1,
        "Image_Group_Number": 1,
    }
    image_fields = {
        field_spec.name: field_spec for field_spec in projection.image_table.columns
    }
    assert image_fields["Image_Metadata_Site"].dtype is int
    assert image_fields["Image_Metadata_ChannelNumber"].dtype is int
    assert image_fields["Image_Metadata_Frame"].dtype is int
    assert image_fields["Image_Metadata_Series"].dtype is int


def test_projection_canonicalizes_physical_source_path(tmp_path: Path) -> None:
    source_directory = tmp_path / "source"
    staging_directory = tmp_path / "staging"
    source_directory.mkdir()
    staging_directory.mkdir()
    source_path = source_directory / "dna.tif"
    Image.fromarray(np.zeros((8, 8), dtype=np.uint8)).save(source_path)
    staged_path = staging_directory / source_path.name
    staged_path.symlink_to(source_path)
    store = RuntimeValueStore()
    dna = _record_image(
        store,
        name="DNA",
        source_path=str(staged_path),
        metadata={"Plate": "20585", "Well": "A01", "Site": "1"},
    )
    batch = RuntimeArtifactBatch(
        input_specs=(dna,),
        records_by_axis={AXIS_ID: store.values()},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    projection = _projection_builder_for_fields(
        (FieldSpec("FileLocation", str, required=False),)
    ).build(
        batch,
        _settings(),
        CPAImageChannelSpec.defaults_for_artifacts(
            (dna,),
            source_binding_plan=CompiledSourceBindingPlan.empty(),
        ),
    )

    row = _external_rows(projection.image_table)[0]
    assert row["Image_PathName_DNA"] == str(source_directory)
    assert row["Image_Metadata_FileLocation"] == source_path.resolve().as_uri()


def test_projection_renders_source_builtins_and_thumbnail_from_declared_image(
    tmp_path: Path,
) -> None:
    source_path = tmp_path / "dna.tif"
    Image.fromarray(np.arange(64, dtype=np.uint16).reshape(8, 8)).save(source_path)
    store = RuntimeValueStore()
    dna = _record_image(
        store,
        name="DNA",
        source_path=str(source_path),
        metadata={
            "Plate": "20585",
            "Well": "A01",
            "Site": "1",
            "ChannelNumber": "1",
        },
    )
    batch = RuntimeArtifactBatch(
        input_specs=(dna,),
        records_by_axis={AXIS_ID: store.values()},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )
    settings = replace(
        _settings(),
        write_image_thumbnails=True,
        thumbnail_image_names=("DNA",),
    )

    projection = _projection_builder().build(
        batch,
        settings,
        CPAImageChannelSpec.defaults_for_artifacts(
            (dna,),
            source_binding_plan=CompiledSourceBindingPlan.empty(),
        ),
    )

    row = _external_rows(projection.image_table)[0]
    assert row["Image_Frame_DNA"] == 0
    assert row["Image_Height_DNA"] == 8
    assert row["Image_Scaling_DNA"] == 65535.0
    assert row["Image_Series_DNA"] == 0
    assert row["Image_URL_DNA"] == source_path.resolve().as_uri()
    assert row["Image_Width_DNA"] == 8
    assert len(row["Image_MD5Digest_DNA"]) == 32
    thumbnail_value = row["Image_Thumbnail_DNA"]
    assert isinstance(thumbnail_value, str)
    thumbnail_png = b64decode(thumbnail_value)
    assert thumbnail_png.startswith(b"\x89PNG\r\n\x1a\n")
    with Image.open(BytesIO(thumbnail_png)) as thumbnail:
        assert thumbnail.mode == "L"
        assert thumbnail.size == (200, 200)
    assert {
        "Image_Frame_DNA",
        "Image_Height_DNA",
        "Image_MD5Digest_DNA",
        "Image_Scaling_DNA",
        "Image_Series_DNA",
        "Image_URL_DNA",
        "Image_Width_DNA",
    } <= {field_spec.name for field_spec in projection.image_table.columns}


def _borrowed_source_export_fixture(
    tmp_path: Path,
    *,
    embedded_tiff: bool = False,
    calibration_scope=None,
):
    """Real source workspace occurrences and measurements, without image records."""
    calibration = tmp_path / ("IllumDNA.tif" if embedded_tiff else "IllumDNA.npy")
    if embedded_tiff:
        import tifffile

        tifffile.imwrite(
            calibration,
            np.ones((3, 5, 7), dtype=np.uint16),
            photometric="minisblack",
            metadata={"axes": "ZYX"},
        )
    else:
        np.save(calibration, np.ones((5, 7), dtype=np.float32))
    sources = []
    source_metadata = []
    for site in (1, 2, 3):
        original = tmp_path / f"dna-{site}.tif"
        Image.fromarray(np.zeros((5, 7), dtype=np.uint16)).save(original)
        metadata = {"well": "A01", "site": str(site), "z_index": "1", "timepoint": "1"}
        source_metadata.append(metadata)
        sources.extend(
            (
                SourcePlaneProjection(
                    address=OpenHCSPlaneAddress.from_values("A01", site, 1, 1, 1),
                    ref=SourcePixelRef("disk", str(original)),
                    source_alias="DNA",
                    source_metadata=metadata,
                ),
                SourceArtifactProjection(
                    address=OpenHCSPlaneAddress.from_values("A01", site, 2, 1, 1),
                    ref=SourcePixelRef(
                        "disk", str(calibration), (site - 1,) if embedded_tiff else ()
                    ),
                    source_alias="IllumDNA",
                    artifact_kind=ImageArtifactType,
                    source_metadata=metadata,
                    execution_scope=calibration_scope,
                ),
            )
        )
    serializer = SourceProjectionMetadataSerializer(SourceSchemaFilenameParser())
    document = {
        "subdirectories": {
            "source": serializer.metadata_dict(
                SourceProjectionSet(tuple(sources)),
                microscope_handler_name="openhcs",
                source_filename_parser_name="source_schema",
                grid_dimensions=[1, 1],
                pixel_size=1.0,
            )
        }
    }
    context = _export_context()
    context.plate_path = tmp_path
    context.microscope_handler = SimpleNamespace(
        source_admission_config=lambda: None,
        metadata_handler=SimpleNamespace(
            source_workspace_metadata_document=lambda _plate_path: document,
        )
    )
    context.filemanager = SimpleNamespace(
        exists=lambda *_args: False,
        source_path=lambda address, backend, *, base_path: address,
    )
    plan = CompiledSourceBindingPlan(
        bindings=(
            NamedSourceBinding(alias="DNA"),
            NamedSourceBinding(
                alias="IllumDNA", projection_role=SourceProjectionRole.SOURCE_ARTIFACT
            ),
        )
    )
    table = MeasurementTable(
        name="ImageMeasurements",
        rows=MeasurementSparseColumnarRows.from_rows(
            tuple(
                {RUNTIME_IMAGE_FIELD: index, "Count_Nuclei": index + 1}
                for index in range(2)
            ),
            fields=(
                FieldSpec(RUNTIME_IMAGE_FIELD, int),
                FieldSpec("Count_Nuclei", int),
            ),
        ),
        subject=MeasurementSubject(MeasurementScope.IMAGE, "Image"),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            component_metadata=tuple(source_metadata[:2]),
        ),
    )
    store = RuntimeValueStore()
    output = ArtifactOutputPlan(
        name=table.name,
        path="/memory/measurements.pkl",
        artifact_type=MeasurementsArtifactType,
    )
    store.record(
        RuntimeValue.normalize(output, table, axis_id="A01"),
        path=output.path,
        backend="memory",
    )
    batch = RuntimeArtifactBatch(
        input_specs=(
            ArtifactSpec.input("DNA", ImageArtifactType),
            ArtifactSpec.input("IllumDNA", ImageArtifactType),
            ArtifactSpec.input(table.name, MeasurementsArtifactType),
        ),
        records_by_axis={"A01": store.values()},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(
            frozenset((AllComponents.CHANNEL,))
        ),
        source_binding_plan=plan,
    )
    builder = CellProfilerAnalystProjectionBuilder(plan, context=context)
    channels = CPAImageChannelSpec.defaults_for_artifacts(
        batch.specs_of_type(ImageArtifactType), source_binding_plan=plan
    )
    return builder, batch, channels, calibration, document


def test_source_only_calibration_occurrences_export_each_executed_site(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    builder, batch, channels, calibration, _document = _borrowed_source_export_fixture(
        tmp_path
    )
    assert batch.records_of_type(ImageArtifactType)["A01"] == ()
    from openhcs.core.source_workspace_projection import VirtualWorkspaceSourceProjection
    monkeypatch.setattr(
        VirtualWorkspaceSourceProjection,
        "load_binding_payloads",
        lambda *_args, **_kwargs: pytest.fail(
            "Source headers must not decode pixel arrays"
        ),
    )

    projection = builder.build(batch, _settings(), channels)

    rows = _external_rows(projection.image_table)
    assert len(rows) == 2  # The third declared source site was never executed.
    for image_number, row in enumerate(rows, start=1):
        assert row["ImageNumber"] == image_number
        assert row["Image_FileName_IllumDNA"] == calibration.name
        assert row["Image_PathName_IllumDNA"] == str(tmp_path)
        assert row["Image_URL_IllumDNA"] == calibration.as_uri()
        assert row["Image_Height_IllumDNA"] == 5
        assert row["Image_Width_IllumDNA"] == 7
        assert row["Image_Frame_IllumDNA"] == row["Image_Series_IllumDNA"] == 0
        assert row["Image_Scaling_IllumDNA"] == 1.0
        assert len(row["Image_MD5Digest_IllumDNA"]) == 32
        assert row["Image_FileName_DNA"] == f"dna-{image_number}.tif"
        assert row["Image_Scaling_DNA"] == 65535.0


def test_source_bound_export_refuses_conflicting_recorded_alias(tmp_path: Path) -> None:
    builder, batch, channels, _calibration, _document = _borrowed_source_export_fixture(
        tmp_path
    )
    other = tmp_path / "different.npy"
    np.save(other, np.ones((5, 7), dtype=np.float32))
    store = RuntimeValueStore()
    output = ArtifactOutputPlan(
        name="IllumDNA", path="/memory/conflict.pkl", artifact_type=ImageArtifactType
    )
    payload = ImagePayloadMetadata(
        source_path=str(other),
        source_component_metadata={
            "well": "A01",
            "site": "1",
            "z_index": "1",
            "timepoint": "1",
        },
    ).attach_to(np.ones((5, 7), dtype=np.float32))
    store.record(
        RuntimeValue.normalize(output, payload, axis_id="A01"),
        path=output.path,
        backend="memory",
    )
    batch = replace(
        batch, records_by_axis={"A01": (*batch.records_by_axis["A01"], *store.values())}
    )
    with pytest.raises(ValueError, match="conflicting values.*Image_FileName_IllumDNA"):
        builder.build(batch, _settings(), channels)


def test_source_bound_export_retains_exact_embedded_tiff_frame_selection(
    tmp_path: Path,
) -> None:
    builder, batch, channels, calibration, _document = _borrowed_source_export_fixture(
        tmp_path, embedded_tiff=True
    )
    rows = _external_rows(builder.build(batch, _settings(), channels).image_table)
    assert tuple(row["Image_Frame_IllumDNA"] for row in rows) == (0, 1)
    assert (
        tuple(row["Image_FileName_IllumDNA"] for row in rows) == (calibration.name,) * 2
    )
    assert (
        tuple(
            (row["Image_Height_IllumDNA"], row["Image_Width_IllumDNA"]) for row in rows
        )
        == ((5, 7),) * 2
    )


def test_source_bound_export_does_not_cross_declared_execution_scope(
    tmp_path: Path,
) -> None:
    from openhcs.core.component_group_scope import RuntimeExecutionAxisScope

    builder, batch, channels, _calibration, _document = _borrowed_source_export_fixture(
        tmp_path, calibration_scope=RuntimeExecutionAxisScope("B01")
    )
    rows = _external_rows(builder.build(batch, _settings(), channels).image_table)
    assert len(rows) == 2
    assert all(row.get("Image_FileName_IllumDNA") is None for row in rows)
    assert all(row["Image_FileName_DNA"] for row in rows)


def test_measurement_provenance_projects_exact_named_contributors_by_site(
    tmp_path: Path,
) -> None:
    source_paths: dict[tuple[int, str], Path] = {}
    aliases = ("DNA", "RNA")
    for site in (1, 2):
        for channel, alias in enumerate(aliases, start=1):
            source_path = tmp_path / f"A01_s{site}_w{channel}.tif"
            Image.fromarray(np.full((4, 5), site * 10 + channel, dtype=np.uint16)).save(
                source_path
            )
            source_paths[(site, alias)] = source_path

    planes = SourceImageProvenancePlanes(
        tuple(
            RuntimeSourceImageProvenancePlane(
                SourceImageIdentity(
                    component_metadata=with_original_source_metadata(
                        {"Plate": "20585", "Well": "A01", "Site": site},
                        {"Plate": "20585", "Well": "A01", "Site": site},
                        path=str(source_paths[(site, "DNA")]),
                    )
                ),
                tuple(
                    SourceImageProvenanceContributor(
                        SourceImageIdentity(
                            str(source_paths[(site, alias)]),
                            with_original_source_metadata(
                                {
                                    "Plate": "20585",
                                    "Well": "A01",
                                    "Site": site,
                                    "ChannelNumber": channel,
                                },
                                {
                                    "Plate": "20585",
                                    "Well": "A01",
                                    "Site": site,
                                    "ChannelNumber": channel,
                                },
                                path=str(source_paths[(site, alias)]),
                            ),
                        ),
                        source_image_name=alias,
                    )
                    for channel, alias in enumerate(aliases, start=1)
                ),
            )
            for site in (1, 2)
        )
    )
    store = RuntimeValueStore()
    measurements = _record_measurements(
        store,
        table=MeasurementTable(
            name="ImageMeasurements",
            rows=MeasurementSparseColumnarRows.from_rows(
                (
                    {RUNTIME_IMAGE_FIELD: 0, "ImageQuality_FocusScore_DNA": 1.0},
                    {RUNTIME_IMAGE_FIELD: 1, "ImageQuality_FocusScore_DNA": 2.0},
                ),
                fields=(
                    FieldSpec(RUNTIME_IMAGE_FIELD, int),
                    FieldSpec("ImageQuality_FocusScore_DNA", float),
                ),
            ),
            subject=MeasurementSubject(MeasurementScope.IMAGE, "Image"),
        ),
        source_image_provenance_planes=planes,
    )
    batch = RuntimeArtifactBatch(
        input_specs=(
            ArtifactSpec.input("DNA", ImageArtifactType),
            ArtifactSpec.input("RNA", ImageArtifactType),
            measurements,
        ),
        records_by_axis={AXIS_ID: store.values()},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(
            frozenset((AllComponents.CHANNEL,))
        ),
    )
    channels = tuple(
        CPAImageChannelSpec(alias=alias, image_name=alias, channel_color="none")
        for alias in aliases
    )

    projection = _projection_builder_for_fields(
        (
            FieldSpec("Plate", str, required=False),
            FieldSpec("Well", str, required=False),
            FieldSpec("Site", int, required=False),
            FieldSpec("ChannelNumber", int, required=False),
            FieldSpec("FileLocation", str, required=False),
            FieldSpec("Frame", int, required=False),
            FieldSpec("Series", int, required=False),
        )
    ).build(
        batch,
        _settings(),
        channels,
    )

    image_rows = _external_rows(projection.image_table)
    assert tuple(
        (
            row["Image_Metadata_Site"],
            row["Image_FileName_DNA"],
            row["Image_FileName_RNA"],
        )
        for row in image_rows
    ) == (
        (1, "A01_s1_w1.tif", "A01_s1_w2.tif"),
        (2, "A01_s2_w1.tif", "A01_s2_w2.tif"),
    )
    assert all(
        row["Image_Width_DNA"] == 5 and row["Image_Width_RNA"] == 5
        for row in image_rows
    )


def test_projection_calculates_declared_per_image_object_mean() -> None:
    store = RuntimeValueStore()
    nuclei = _record_measurements(
        store,
        table=MeasurementTable(
            name="NucleiMeasurements",
            rows=MeasurementProjectedColumnarRows(
                {
                    RUNTIME_IMAGE_FIELD: (0, 0),
                    "ObjectNumber": (1, 2),
                    "AreaShape_Area": (24.0, 36.0),
                },
                fields=(
                    FieldSpec(RUNTIME_IMAGE_FIELD, int),
                    FieldSpec("ObjectNumber", int),
                    FieldSpec("AreaShape_Area", float),
                ),
            ),
            subject=MeasurementSubject(
                MeasurementScope.OBJECT,
                "Nuclei",
                "ObjectNumber",
            ),
        ),
    )
    batch = RuntimeArtifactBatch(
        input_specs=(nuclei,),
        records_by_axis={AXIS_ID: store.values()},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    projection = _projection_builder().build(
        batch,
        replace(_settings(), calculate_per_image_mean=True),
        (),
    )

    assert _external_rows(projection.image_table)[0][
        "Mean_Nuclei_AreaShape_Area"
    ] == pytest.approx(30.0)
    aggregate_field = next(
        field_spec
        for field_spec in projection.image_table.columns
        if field_spec.name == "Mean_Nuclei_AreaShape_Area"
    )
    assert aggregate_field.dtype is float


def test_sqlite_declares_empty_image_object_and_experiment_properties_tables() -> None:
    batch = RuntimeArtifactBatch(
        input_specs=(),
        records_by_axis={AXIS_ID: ()},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )
    settings = CellProfilerDatabaseExportSettings(
        sqlite_file="QC.db",
        experiment_name="QC",
        table_prefix="QC_",
        object_table_mode=CellProfilerObjectTableMode.COMBINED,
        selected_objects=None,
        wants_properties_file=True,
        wants_relationship_tables=False,
        location_object="None",
        classification_type="image",
    )
    projection = _projection_builder().build(batch, settings, ())

    (properties_file,) = CPAPropertiesRenderer().render(settings, (), projection)
    assert properties_file.properties["object_id"] == "ObjectNumber"
    assert properties_file.properties["cell_x_loc"] == "None_Location_Center_X"
    assert properties_file.properties["cell_y_loc"] == "None_Location_Center_Y"
    assert properties_file.properties["cell_z_loc"] == "None_Location_Center_Z"

    connection = sqlite3.connect(":memory:")
    try:
        connection.deserialize(CPASQLiteRenderer().render(projection, settings))
        table_names = {
            row[0]
            for row in connection.execute(
                "SELECT name FROM sqlite_master "
                "WHERE type = 'table' AND name NOT LIKE 'sqlite_%'"
            )
        }
        assert table_names == {
            "Experiment",
            "Experiment_Properties",
            "QC_Per_Experiment",
            "QC_Per_Image",
            "QC_Per_Object",
        }
        assert tuple(
            row[1] for row in connection.execute('PRAGMA table_info("QC_Per_Object")')
        ) == ("ImageNumber", "ObjectNumber")
        assert dict(
            connection.execute(
                'SELECT field, value FROM "Experiment_Properties" '
                'WHERE field IN ("object_id", "cell_x_loc", "cell_y_loc", "cell_z_loc")'
            )
        ) == {
            "object_id": "ObjectNumber",
            "cell_x_loc": "None_Location_Center_X",
            "cell_y_loc": "None_Location_Center_Y",
            "cell_z_loc": "None_Location_Center_Z",
        }
    finally:
        connection.close()


def test_projection_exports_normalized_identify_primary_objects_image_number() -> None:
    store = RuntimeValueStore()
    measurements = _record_measurements(
        store,
        table=MeasurementTable(
            name="IdentifyPrimaryObjects_1_measurements",
            rows=MeasurementProjectedColumnarRows(
                {
                    MeasurementRowAxisField.SLICE_INDEX.value: (0, 0),
                    MeasurementRowAxisField.FEATURE_NAME.value: (
                        "Count_Nuclei",
                        "Threshold_FinalThreshold_Nuclei",
                    ),
                    MeasurementRowValueField.RESULT_VALUE.value: (2, 0.2),
                },
                fields=(
                    FieldSpec(MeasurementRowAxisField.SLICE_INDEX.value, int),
                    FieldSpec(MeasurementRowAxisField.FEATURE_NAME.value, str),
                    FieldSpec(MeasurementRowValueField.RESULT_VALUE.value, float),
                ),
            ),
            subject=MeasurementSubject(MeasurementScope.IMAGE, "Image"),
        ),
    )
    image_spec = ArtifactSpec.input("DNA", ImageArtifactType)
    batch = RuntimeArtifactBatch(
        input_specs=(image_spec, measurements),
        records_by_axis={AXIS_ID: store.values()},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    projection = _projection_builder().build(
        batch,
        _settings(),
        CPAImageChannelSpec.defaults_for_artifacts(
            (image_spec,),
            source_binding_plan=CompiledSourceBindingPlan.empty(),
        ),
    )

    image_rows = _external_rows(projection.image_table)
    assert tuple(row["ImageNumber"] for row in image_rows) == (1,)
    assert image_rows[0] == {
        "ImageNumber": 1,
        "Image_Count_Nuclei": 2,
        "Image_Threshold_FinalThreshold_Nuclei": 0.2,
        "Image_Group_Index": 1,
        "Image_Group_Length": 1,
        "Image_Group_Number": 1,
    }


def test_projection_merges_axisless_and_slice_qualified_object_measurements() -> None:
    store = RuntimeValueStore()
    measurements = _record_measurements(
        store,
        table=MeasurementTable(
            name="ResizeObjects_1_measurements",
            rows=MeasurementSparseColumnarRows.from_rows(
                (
                    {
                        RUNTIME_IMAGE_FIELD: 0,
                        "ObjectNumber": 1,
                        "AreaShape_Area": 24.0,
                    },
                    {
                        "ObjectNumber": 1,
                        "Children_Nuclei_Count": 2,
                    },
                ),
                fields=(
                    FieldSpec(RUNTIME_IMAGE_FIELD, int),
                    FieldSpec("ObjectNumber", int),
                    FieldSpec("AreaShape_Area", float, required=False),
                    FieldSpec("Children_Nuclei_Count", int, required=False),
                ),
            ),
            subject=MeasurementSubject(
                MeasurementScope.OBJECT,
                "Cells",
                "ObjectNumber",
            ),
        ),
    )
    image_spec = ArtifactSpec.input("DNA", ImageArtifactType)
    batch = RuntimeArtifactBatch(
        input_specs=(image_spec, measurements),
        records_by_axis={AXIS_ID: store.values()},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    projection = _projection_builder().build(
        batch,
        _settings(),
        CPAImageChannelSpec.defaults_for_artifacts(
            (image_spec,),
            source_binding_plan=CompiledSourceBindingPlan.empty(),
        ),
    )

    assert _field_rows(projection.object_tables[0]) == (
        {
            "ImageNumber": 1,
            "Cells_Number_Object_Number": 1,
            "Cells_AreaShape_Area": 24.0,
            "Cells_Children_Nuclei_Count": 2,
        },
    )


def test_projection_uses_declared_row_identity_aliases_as_structural_fields() -> None:
    store = RuntimeValueStore()
    shape_measurements = _record_measurements(
        store,
        table=MeasurementTable(
            name="CellsShape",
            rows=MeasurementProjectedColumnarRows(
                {
                    RUNTIME_IMAGE_FIELD: (0,),
                    MeasurementRowAxisField.OBJECT_LABEL.value: (1,),
                    "AreaShape_Area": (24.0,),
                },
                fields=(
                    FieldSpec(RUNTIME_IMAGE_FIELD, int),
                    FieldSpec(MeasurementRowAxisField.OBJECT_LABEL.value, int),
                    FieldSpec("AreaShape_Area", float),
                ),
            ),
            subject=MeasurementSubject(MeasurementScope.OBJECT, "Cells"),
        ),
    )
    identity_alias_measurements = _record_measurements(
        store,
        table=MeasurementTable(
            name="CellsIdentityAlias",
            rows=MeasurementProjectedColumnarRows(
                {
                    RUNTIME_IMAGE_FIELD: (0,),
                    "Number_Object_Number": (1,),
                    "Children_Nuclei_Count": (2,),
                },
                fields=(
                    FieldSpec(RUNTIME_IMAGE_FIELD, int),
                    FieldSpec("Number_Object_Number", int),
                    FieldSpec("Children_Nuclei_Count", int),
                ),
            ),
            subject=MeasurementSubject(MeasurementScope.OBJECT, "Cells"),
        ),
    )
    image_spec = ArtifactSpec.input("DNA", ImageArtifactType)
    batch = RuntimeArtifactBatch(
        input_specs=(image_spec, shape_measurements, identity_alias_measurements),
        records_by_axis={AXIS_ID: store.values()},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    projection = _projection_builder().build(
        batch,
        _settings(),
        CPAImageChannelSpec.defaults_for_artifacts(
            (image_spec,),
            source_binding_plan=CompiledSourceBindingPlan.empty(),
        ),
    )

    object_table = projection.object_tables[0]
    assert tuple(
        field
        for field in object_table.columns
        if field.name == "Cells_Number_Object_Number"
    ) == (
        FieldSpec("Cells_Number_Object_Number", int),
    )
    assert _field_rows(object_table) == (
        {
            "ImageNumber": 1,
            "Cells_Number_Object_Number": 1,
            "Cells_AreaShape_Area": 24.0,
            "Cells_Children_Nuclei_Count": 2,
        },
    )


def test_projection_rejects_image_channels_absent_from_contract() -> None:
    batch = RuntimeArtifactBatch(
        input_specs=(),
        records_by_axis={AXIS_ID: ()},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )

    with pytest.raises(
        ValueError, match="absent from the exact runtime artifact contract"
    ):
        _projection_builder().build(
            batch,
            _settings(),
            (CPAImageChannelSpec("DNA", "DNA", "blue"),),
        )


def test_sqlite_and_properties_render_from_projection_without_execution_context() -> (
    None
):
    store = RuntimeValueStore()
    image_measurements = _record_measurements(
        store,
        table=MeasurementTable(
            name="ImageMeasurements",
            rows=MeasurementSparseColumnarRows.from_rows(
                ({RUNTIME_IMAGE_FIELD: 0, "Count_Nuclei": 2},),
                fields=(
                    FieldSpec(RUNTIME_IMAGE_FIELD, int),
                    FieldSpec("Count_Nuclei", int),
                ),
            ),
            subject=MeasurementSubject(MeasurementScope.IMAGE, "Image"),
        ),
    )
    nuclei = _record_measurements(
        store,
        table=MeasurementTable(
            name="NucleiMeasurements",
            rows=MeasurementProjectedColumnarRows(
                {
                    RUNTIME_IMAGE_FIELD: (0, 0),
                    "ObjectNumber": (1, 2),
                    "AreaShape_Area": (24.0, 36.0),
                },
                fields=(
                    FieldSpec(RUNTIME_IMAGE_FIELD, int),
                    FieldSpec("ObjectNumber", int),
                    FieldSpec("AreaShape_Area", float),
                ),
            ),
            subject=MeasurementSubject(
                MeasurementScope.OBJECT, "Nuclei", "ObjectNumber"
            ),
        ),
    )
    image_spec = ArtifactSpec.input("DNA", ImageArtifactType)
    batch = RuntimeArtifactBatch(
        input_specs=(image_spec, image_measurements, nuclei),
        records_by_axis={AXIS_ID: store.values()},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )
    settings = _settings()
    channels = (CPAImageChannelSpec("DNA", "DNA", "blue"),)
    projection = _projection_builder().build(
        batch,
        settings,
        channels,
    )

    sqlite_bytes = CPASQLiteRenderer().render(projection, settings)
    assert sqlite_bytes.startswith(b"SQLite format 3\x00")
    connection = sqlite3.connect(":memory:")
    try:
        connection.deserialize(sqlite_bytes)
        table_names = tuple(
            row[0]
            for row in connection.execute(
                "SELECT name FROM sqlite_master "
                "WHERE type = 'table' AND name NOT LIKE 'sqlite_%' ORDER BY name"
            )
        )
        assert table_names == (
            "CPA_Per_Experiment",
            "CPA_Per_Image",
            "CPA_Per_Nuclei",
            "Experiment",
            "Experiment_Properties",
        )
        assert connection.execute(
            'SELECT "Nuclei_AreaShape_Area" FROM "CPA_Per_Nuclei" '
            'ORDER BY "Nuclei_Number_Object_Number"'
        ).fetchall() == [(24.0,), (36.0,)]
    finally:
        connection.close()

    (properties_file,) = CPAPropertiesRenderer().render(
        settings,
        channels,
        projection,
    )
    assert properties_file.file_name == "DefaultDB_CPA_Nuclei.properties"
    assert properties_file.properties["db_type"] == "sqlite"
    assert properties_file.properties["db_sqlite_file"] == "DefaultDB.db"
    assert properties_file.properties["image_table"] == "CPA_Per_Image"
    assert properties_file.properties["object_table"] == "CPA_Per_Nuclei"
    assert properties_file.properties["object_id"] == "Nuclei_Number_Object_Number"
    assert properties_file.properties["image_path_cols"] == "Image_PathName_DNA"
    assert properties_file.properties["image_file_cols"] == "Image_FileName_DNA"
    assert properties_file.properties["cell_x_loc"] == "Nuclei_Location_Center_X"
    assert properties_file.properties["cell_y_loc"] == "Nuclei_Location_Center_Y"
    assert properties_file.properties["cell_z_loc"] == "Nuclei_Location_Center_Z"


def test_module_parses_typed_settings_and_private_repeated_image_groups() -> None:
    module = _database_module(
        (
            ("Add a prefix to table names?", "Yes"),
            ("Table prefix", "Adv_"),
            ("Export measurements for all objects to the database?", "Select..."),
            ("Select the objects", "Nuclei, Cells"),
            ("Include information for all images, using default values?", "No"),
            ("Properties image group count", "2"),
            ("Select an image to include", "DNA"),
            ("Use the image name for the display?", "Yes"),
            ("Image name", "DNA display"),
            ("Channel color", "blue"),
            ("Select an image to include", "RNA"),
            ("Use the image name for the display?", "No"),
            ("Image name", "ignored"),
            ("Channel color", "green"),
        )
    )

    bound = ExportToDatabaseModule.bind_settings(module, binder=SettingsBinder())

    assert bound.kwargs["table_prefix"] == "Adv_"
    assert bound.kwargs["object_table_mode"] is CellProfilerObjectTableMode.PER_OBJECT
    assert bound.kwargs["selected_objects"] == ("Nuclei", "Cells")
    assert bound.kwargs["image_channels"] == (
        CPAImageChannelSpec("DNA", "DNA display", "blue"),
        CPAImageChannelSpec("RNA", "RNA", "green"),
    )
    assert bound.unmapped_kwargs == {}


def test_module_contract_selects_ordered_tables_and_cpa_images_and_declares_bundle() -> (
    None
):
    module = _database_module(
        (("Include information for all images, using default values?", "Yes"),)
    )
    available = ArtifactSpecCollection(
        (
            ArtifactSpec.output("Images_measurements", MeasurementsArtifactType),
            ArtifactSpec.input("DNA", ImageArtifactType),
            ArtifactSpec.output("Nuclei_measurements", MeasurementsArtifactType),
            ArtifactSpec.output("RNA", ImageArtifactType),
            ArtifactSpec.output("Nuclei_relationships", RelationshipsArtifactType),
        )
    )
    contract = ExportToDatabaseModule.callable_contract(
        module=module,
        invocation_key=FunctionInvocationKey("export_to_database", "default", 0),
        step_context=ArtifactDeclarationStepContext(
            step_name="ExportToDatabase",
            step_index=4,
            source_bindings=StepSourceBindingsConfig(
                enabled=True,
                bindings=(
                    NamedSourceBinding(
                        alias="DNA",
                        projection_role=SourceProjectionRole.SOURCE_ARTIFACT,
                    ),
                ),
            ),
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

    assert contract.artifact_inputs.names() == (
        "Images_measurements",
        "DNA",
        "Nuclei_measurements",
        "RNA",
        "Nuclei_relationships",
    )
    (output,) = contract.artifact_outputs
    assert output.artifact_type is SpecialArtifactType
    assert output.materialization is not None
    assert isinstance(output.materialization.outputs[0], FileBundleOptions)

    callable_contract = CallableContract.from_callable(export_to_database)
    assert callable_contract.execution_scope is FunctionStepExecutionScope.PLATE
    assert callable_contract.processing_contract is None
    assert callable_contract.runtime_adapter is None
    assert callable_contract.metadata.runtime_bound_parameters == (
        RuntimeArtifactBatch,
    )


@pytest.mark.parametrize("workspace", [False, True])
def test_raw_callable_uses_batch_source_plan_with_sibling_plate_step(
    workspace: bool,
) -> None:
    store = RuntimeValueStore()
    measurements = _record_measurements(
        store,
        table=MeasurementTable(
            name="Images",
            rows=MeasurementSparseColumnarRows.from_rows(
                ({RUNTIME_IMAGE_FIELD: 0, "Count": 2},),
                fields=(
                    FieldSpec(RUNTIME_IMAGE_FIELD, int),
                    FieldSpec("Count", int),
                ),
            ),
            subject=MeasurementSubject(MeasurementScope.IMAGE, "Image"),
        ),
    )
    image_spec = ArtifactSpec.input("DNA", ImageArtifactType)
    batch = RuntimeArtifactBatch(
        input_specs=(image_spec, measurements),
        records_by_axis={AXIS_ID: store.values()},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
    )
    context = _export_context()
    context.step_plans[1] = CompiledStepPlan(
        step_index=1,
        step_name="SiblingPlateExport",
        step_type="FunctionStep",
        axis_id=AXIS_ID,
        source_binding_plan=CompiledSourceBindingPlan(
            metadata_fields=(FieldSpec("SiblingOnly", str, required=False),),
        ),
        compiled_function_pattern=compile_function_pattern(
            export_to_database,
            {},
            {},
        ),
    )

    from openhcs.interop.cellprofiler.workspace_export import (
        CPAWorkspacePanel,
        CPAWorkspaceAxis,
    )

    panels = (
        (
            CPAWorkspacePanel.from_settings(
                "Histogram",
                CPAWorkspaceAxis.from_settings("Image", "None", "Count", "ImageNumber"),
                CPAWorkspaceAxis.from_settings("Image", "None", "None", "ImageNumber"),
            ),
        )
        if workspace
        else ()
    )
    bundle = export_to_database(
        artifact_batch=batch,
        context=context,
        sqlite_file="analysis.sqlite",
        experiment_name="Example",
        add_table_prefix=True,
        table_prefix="CPA_",
        wants_workspace_file=workspace,
        workspace_panels=panels,
    )

    assert tuple(bundle) == (
        ("analysis.sqlite", "analysis_CPA.properties", "analysis_CPA.workspace")
        if workspace
        else ("analysis.sqlite", "analysis_CPA.properties")
    )
    if workspace:
        assert CPAWorkspacePanel.parse_workspace(bundle["analysis_CPA.workspace"]) == (
            ("Histogram", (("x-axis", "Image_Count"), ("table", "CPA_Per_Image"))),
        )
    assert isinstance(bundle["analysis.sqlite"], bytes)
    assert str(bundle["analysis_CPA.properties"]).startswith("db_type = sqlite\n")


def _settings() -> CellProfilerDatabaseExportSettings:
    return CellProfilerDatabaseExportSettings(
        sqlite_file="DefaultDB.db",
        experiment_name="Experiment",
        table_prefix="CPA_",
        object_table_mode=CellProfilerObjectTableMode.PER_OBJECT,
        selected_objects=None,
        wants_properties_file=True,
        wants_relationship_tables=True,
    )


def _database_module(
    extra_records: tuple[tuple[str, str], ...] = (),
) -> ModuleBlock:
    base_records = (
        ("Database type", "SQLite"),
        ("Name the SQLite database file", "analysis.db"),
        ("Experiment name", "AdvancedSegmentation"),
        ("Add a prefix to table names?", "No"),
        ("Table prefix", "Unused_"),
        ("Create a CellProfiler Analyst properties file?", "Yes"),
        ("Export measurements for all objects to the database?", "All"),
        ("Select the objects", ""),
        ("Export object relationships?", "Yes"),
        (
            "Create one table per object, a single object table or a single object view?",
            "One table per object type",
        ),
        ("Calculate the per-image mean values of object measurements?", "No"),
        ("Calculate the per-image median values of object measurements?", "No"),
        (
            "Calculate the per-image standard deviation values of object measurements?",
            "No",
        ),
        ("Calculate the per-well mean values of object measurements?", "No"),
        ("Calculate the per-well median values of object measurements?", "No"),
        (
            "Calculate the per-well standard deviation values of object measurements?",
            "No",
        ),
        ("Maximum # of characters in a column name", "64"),
        (
            "Enter an image url prepend if you plan to access your files via http",
            "",
        ),
        ("Write image thumbnails directly to the database?", "No"),
        ("Select the images for which you want to save thumbnails", ""),
        ("Auto-scale thumbnail pixel intensities?", "Yes"),
        ("Select the plate type", "384"),
        ("Select the plate metadata", "Plate"),
        ("Select the well metadata", "Well"),
        ("Include information for all images, using default values?", "Yes"),
        ("Properties image group count", "1"),
        ("Select an image to include", "None"),
        ("Use the image name for the display?", "Yes"),
        ("Image name", "Channel1"),
        ("Channel color", "red"),
        ("Properties group field count", "1"),
        ("Do you want to add group fields?", "No"),
        ("Enter the name of the group", ""),
        (
            "Enter the per-image columns which define the group, separated by commas",
            "ImageNumber, Image_Metadata_Plate, Image_Metadata_Well",
        ),
        ("Properties filter field count", "0"),
        ("Do you want to add filter fields?", "No"),
        ("Automatically create a filter for each plate?", "No"),
        (
            "Enter a phenotype class table name if using the Classifier tool in CellProfiler Analyst",
            "",
        ),
        ("Overwrite without warning?", "Never"),
        ("Access CellProfiler Analyst images via URL?", "No"),
        ("Select the classification type", "Object"),
        ("Workspace measurement count", "1"),
        ("Create a CellProfiler Analyst workspace file?", "No"),
        ("Select the measurement display tool", "ScatterPlot"),
        ("Type of measurement to plot on the X-axis", "Image"),
        ("Enter the object name", "None"),
        ("Select the X-axis measurement", "None"),
        ("Select the X-axis index", "ImageNumber"),
        ("Type of measurement to plot on the Y-axis", "Image"),
        ("Enter the object name", "None"),
        ("Select the Y-axis measurement", "None"),
        ("Select the Y-axis index", "ImageNumber"),
    )
    replacements = {name for name, _value in extra_records}
    records = (
        tuple((name, value) for name, value in base_records if name not in replacements)
        + extra_records
    )
    setting_records = [ModuleSetting(name, value) for name, value in records]
    return ModuleBlock(
        name="ExportToDatabase",
        module_num=9,
        setting_records=setting_records,
    )


def _record_measurements(
    store: RuntimeValueStore,
    *,
    table: MeasurementTable,
    source_image_provenance_planes: SourceImageProvenancePlanes | None = None,
) -> ArtifactSpec:
    table = table.replace_fields(
        source_image_provenance_planes=(
            source_image_provenance_planes
            if source_image_provenance_planes is not None
            else SourceImageProvenancePlanes.from_components(
                component_metadata=({"well": "A01", "site": "1"},)
            )
        )
    )
    output_plan = ArtifactOutputPlan(
        name=table.name,
        path=f"/memory/{table.name}.pkl",
        artifact_type=MeasurementsArtifactType,
    )
    store.record(
        RuntimeValue.normalize(output_plan, table, axis_id=AXIS_ID),
        path=output_plan.path,
        backend="memory",
    )
    return ArtifactSpec.input(table.name, MeasurementsArtifactType)


def _record_image(
    store: RuntimeValueStore,
    *,
    name: str,
    source_path: str,
    metadata: dict[str, str],
) -> ArtifactSpec:
    output_plan = ArtifactOutputPlan(
        name=name,
        path=f"/memory/{name}.pkl",
        artifact_type=ImageArtifactType,
    )
    source_metadata = with_original_source_metadata(
        metadata,
        metadata,
        path=source_path,
    )
    payload = ImagePayloadMetadata(
        source_path=source_path,
        source_component_metadata=source_metadata,
    ).attach_to(np.zeros((8, 8), dtype=np.uint8))
    store.record(
        RuntimeValue.normalize(output_plan, payload, axis_id=AXIS_ID),
        path=output_plan.path,
        backend="memory",
    )
    return ArtifactSpec.input(name, ImageArtifactType)


def _record_relationship(
    store: RuntimeValueStore,
    *,
    relationship: ObjectRelationship,
) -> ArtifactSpec:
    output_plan = ArtifactOutputPlan(
        name=relationship.name,
        path=f"/memory/{relationship.name}.pkl",
        artifact_type=RelationshipsArtifactType,
    )
    store.record(
        RuntimeValue.normalize(output_plan, relationship, axis_id=AXIS_ID),
        path=output_plan.path,
        backend="memory",
    )
    return ArtifactSpec.input(relationship.name, RelationshipsArtifactType)


def _external_rows(
    table: CellProfilerProjectedTable,
) -> tuple[dict[str, object], ...]:
    return tuple(dict(row) for row in table.rows)


def _field_rows(
    table: CellProfilerProjectedTable,
) -> tuple[dict[str, object], ...]:
    return tuple(dict(row) for row in table.rows)


def test_database_projection_includes_derived_grid_measurements() -> None:
    from openhcs.core.artifacts import SpatialGridArtifactType
    from openhcs.core.runtime_spatial_grid import SpatialGrid
    from openhcs.core.source_image_provenance import SourceImageProvenance

    grid = SpatialGrid(
        name="Grid",
        rows=8,
        columns=12,
        x_spacing=102.5,
        y_spacing=103.25,
        x_origin=71,
        y_origin=57,
        source_provenance=SourceImageProvenance(
            source_component_metadata={"site": "1"}
        ),
    )
    plan = ArtifactOutputPlan(
        name="Grid", path="/memory/Grid.pkl", artifact_type=SpatialGridArtifactType
    )
    store = RuntimeValueStore()
    record = store.record(
        RuntimeValue.normalize(plan, grid, axis_id=AXIS_ID),
        path=plan.path,
        backend="memory",
    )
    batch = RuntimeArtifactBatch(
        input_specs=(ArtifactSpec.input("Grid", SpatialGridArtifactType),),
        records_by_axis={AXIS_ID: (record,)},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )
    projection = _projection_builder().build(batch, _settings(), ())
    (row,) = _external_rows(projection.image_table)
    assert row["ImageNumber"] == 1
    assert {name: value for name, value in row.items() if "DefinedGrid" in name} == {
        "Image_DefinedGrid_Grid_Columns": 12,
        "Image_DefinedGrid_Grid_Rows": 8,
        "Image_DefinedGrid_Grid_XLocationOfLowestXSpot": 71,
        "Image_DefinedGrid_Grid_XSpacing": 102.5,
        "Image_DefinedGrid_Grid_YLocationOfLowestYSpot": 57,
        "Image_DefinedGrid_Grid_YSpacing": 103.25,
    }


def test_repeated_source_contributors_share_physical_projection(tmp_path, monkeypatch):
    from collections import defaultdict
    import openhcs.interop.cellprofiler.analyst_export as export
    from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
    from openhcs.core.source_image_provenance import SourceImageProvenance

    source = tmp_path / "DNA.tif"
    import tifffile
    tifffile.imwrite(
        source, np.arange(192, dtype=np.uint16).reshape(3, 8, 8),
        photometric="minisblack", metadata={"axes": "ZYX"},
    )
    provenance = SourceImageProvenance(
        source_path=str(source), source_component_metadata={"well": "A01", "site": "1"},
        source_image_names=("DNA",),
    )
    owner = CPATableRowProjection(
        CellProfilerDatabaseColumnDialect(),
        CellProfilerImageSetNumbering(SourceImageSetIdentityPolicy()),
    )
    rows, metadata = {}, defaultdict(list)
    manufacture = export._source_image_projection_values
    calls = []
    def counted(*args, **kwargs):
        calls.append(args[0])
        return manufacture(*args, **kwargs)
    monkeypatch.setattr(export, "_source_image_projection_values", counted)
    for _ in range(3):
        owner.collect_image_provenance(
            provenance, scope=RuntimeExecutionAxisScope(AXIS_ID), source_image_name="DNA",
            image_rows_by_number=rows, source_metadata_by_image_number=metadata,
        )
    assert calls == [source]
    assert len(metadata[1]) == 3  # Every contributor's correlation evidence survives.
    conflicting = provenance.with_source_path(str(tmp_path / "other.tif"))
    with pytest.raises(ValueError, match="conflicting values"):
        owner.collect_image_provenance(
            conflicting, scope=RuntimeExecutionAxisScope(AXIS_ID), source_image_name="DNA",
            image_rows_by_number=rows, source_metadata_by_image_number=metadata,
        )

    with pytest.raises(ValueError, match="conflicting values"):
        owner.collect_image_provenance(
            provenance, scope=RuntimeExecutionAxisScope(AXIS_ID), source_image_name="DNA",
            image_rows_by_number=rows, source_metadata_by_image_number=metadata,
            source_axis_indices=(1,),
        )
    assert calls == [source]  # Explicit frame admission still rejects contradiction.


def test_produced_thumbnail_uses_named_pixels_not_measurement_source(tmp_path, monkeypatch):
    import openhcs.interop.cellprofiler.analyst_export as export
    source = tmp_path / "DNA.tif"
    Image.fromarray(np.arange(64, dtype=np.uint8).reshape(8, 8)).save(source)
    store = RuntimeValueStore()
    dna = _record_image(store, name="DNA", source_path=str(source), metadata={"well": "A01", "site": "1"})
    planes = SourceImageProvenancePlanes.from_components(
        paths=(str(source),), component_metadata=({"well": "A01", "site": "1"},),
    )
    measurements = tuple(_record_measurements(
        store, table=MeasurementTable(
            name=f"Measurements{index}", source_image_names=("DNA",),
            subject=MeasurementSubject(MeasurementScope.IMAGE, "Image"),
            rows=MeasurementSparseColumnarRows.from_rows(
                ({RUNTIME_IMAGE_FIELD: 0, f"Value{index}": float(index)},),
                fields=(FieldSpec(RUNTIME_IMAGE_FIELD, int), FieldSpec(f"Value{index}", float)),
            ),
        ), source_image_provenance_planes=planes,
    ) for index in range(3))
    batch = RuntimeArtifactBatch(
        input_specs=(dna, *measurements), records_by_axis={AXIS_ID: store.values()},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )
    settings = replace(_settings(), write_image_thumbnails=True, thumbnail_image_names=("DNA",), auto_scale_thumbnail_intensities=False)
    encode = export._thumbnail_png_base64
    pixels = []
    def counted(image, **kwargs):
        pixels.append(np.asarray(image).copy())
        return encode(image, **kwargs)
    monkeypatch.setattr(export, "_thumbnail_png_base64", counted)
    projection = _projection_builder().build(batch, settings, (CPAImageChannelSpec(alias="DNA", image_name="DNA", channel_color="none"),))
    assert len(pixels) == 1
    assert np.array_equal(pixels[0], np.zeros((8, 8), dtype=np.uint8))
    assert _external_rows(projection.image_table)[0]["Image_Thumbnail_DNA"] == encode(pixels[0], auto_scale=False)


def test_source_bound_thumbnail_only_ref_preserves_executed_sites(tmp_path):
    builder, batch, _channels, calibration, _document = _borrowed_source_export_fixture(tmp_path)
    builder.context.filemanager.load_batch = lambda paths, _backend: [
        np.load(calibration) for _path in paths
    ]
    builder.context.filemanager.physical_source_path = lambda address, _backend, *, base_path: address
    settings = replace(
        _settings(), write_image_thumbnails=True, thumbnail_image_names=("IllumDNA",),
        auto_scale_thumbnail_intensities=False,
    )
    projection = builder.build(batch, settings, ())
    rows = _external_rows(projection.image_table)
    assert len(rows) == 2  # The third declared source occurrence was not executed.
    assert all(row["Image_Thumbnail_IllumDNA"] for row in rows)
    assert all("Image_FileName_IllumDNA" not in row for row in rows)
    disabled = replace(settings, write_image_thumbnails=False, thumbnail_image_names=("Missing",))
    assert len(_external_rows(builder.build(batch, disabled, ()).image_table)) == 2
