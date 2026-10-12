import numpy as np
from openhcs.core.materialization.persistence import TerminalMaterializationSpec
from polystore.filemanager import FileManager
from polystore.memory import MemoryStorageBackend

from openhcs.core.artifacts.plans import ArtifactInputPlan
from openhcs.core.artifacts.specs import ArtifactSpec
from openhcs.core.artifacts.kinds import (
    ImageArtifactType,
    MeasurementsArtifactType,
    ObjectLabelsArtifactType,
)
from openhcs.core.pipeline.artifact_planning import (
    AutomaticArtifactOutputMaterializationStrategy,
    ArtifactOutputMaterializationPlanner,
)
from openhcs.core.runtime_exports import RuntimeExportExpectation
from openhcs.core.materialization import (
    CsvOptions,
    ImageFileOptions,
    NameByArtifactName,
    MaterializationSpec,
    ROIOptions,
    materialize,
)
from tests.materialization_plans import output_plan as materialization_output_plan


class DerivedImageArtifactType(ImageArtifactType):
    """Test artifact proving image-family policy follows nominal inheritance."""

    value = None


def test_terminal_image_materialization_strategy_owns_nominal_subclasses() -> None:
    strategy = AutomaticArtifactOutputMaterializationStrategy.for_context(
        DerivedImageArtifactType,
    )

    materialization = strategy.materialization()

    assert isinstance(materialization, TerminalMaterializationSpec)
    assert materialization.outputs == (ImageFileOptions(filename_suffix=".tif"),)
    assert not materialization.participates_in_runtime_export_observation()


def test_terminal_image_output_gets_explicit_tiff_materialization() -> None:
    output = ArtifactSpec.output("Corrected", ImageArtifactType)

    materialization = ArtifactOutputMaterializationPlanner.materialization_for(
        output,
        (),
    )

    assert isinstance(materialization, TerminalMaterializationSpec)
    assert materialization.outputs == (ImageFileOptions(filename_suffix=".tif"),)


def test_consumed_image_output_remains_unmaterialized() -> None:
    output = ArtifactSpec.output("Intermediate", ImageArtifactType)

    materialization = ArtifactOutputMaterializationPlanner.materialization_for(
        output,
        (output.ref().for_plan_type(ArtifactInputPlan),),
    )

    assert materialization is None


def test_object_label_output_gets_terminal_roi_and_label_materialization() -> None:
    output = ArtifactSpec.output("Cells", ObjectLabelsArtifactType)

    materialization = ArtifactOutputMaterializationPlanner.materialization_for(
        output,
        (),
    )

    assert isinstance(materialization, TerminalMaterializationSpec)
    assert materialization.outputs == (
        ROIOptions(
            min_area=1,
            filename_identity=NameByArtifactName,
        ),
        ImageFileOptions(
            filename_suffix=".labels.tif",
            filename_identity=NameByArtifactName,
        ),
    )
    assert materialization.participates_in_persistent_materialization()
    assert not materialization.participates_in_runtime_export_observation()


def test_consumed_object_label_output_retains_terminal_materialization() -> None:
    output = ArtifactSpec.output("Cells", ObjectLabelsArtifactType)

    materialization = ArtifactOutputMaterializationPlanner.materialization_for(
        output,
        (output.ref().for_plan_type(ArtifactInputPlan),),
    )

    assert isinstance(materialization, TerminalMaterializationSpec)


def test_terminal_measurement_output_gets_artifact_named_csv_materialization() -> None:
    output = ArtifactSpec.output("CellMeasurements", MeasurementsArtifactType)

    materialization = ArtifactOutputMaterializationPlanner.materialization_for(
        output,
        (),
    )

    assert isinstance(materialization, TerminalMaterializationSpec)
    assert materialization.outputs == (
        CsvOptions(
            filename_identity=NameByArtifactName,
        ),
    )


def test_consumed_measurement_output_remains_unmaterialized() -> None:
    output = ArtifactSpec.output("Intermediate", MeasurementsArtifactType)

    materialization = ArtifactOutputMaterializationPlanner.materialization_for(
        output,
        (output.ref().for_plan_type(ArtifactInputPlan),),
    )

    assert materialization is None


def test_explicit_output_materialization_remains_authoritative() -> None:
    explicit = MaterializationSpec(ImageFileOptions(filename_suffix=".npy"))
    output = ArtifactSpec.output(
        "Saved",
        ImageArtifactType,
        materialization=explicit,
    )

    assert (
        ArtifactOutputMaterializationPlanner.materialization_for(output, ()) is explicit
    )
    assert explicit.participates_in_runtime_export_observation()


def test_runtime_export_expectation_excludes_terminal_persistence() -> None:
    terminal = ArtifactSpec.output(
        "Terminal",
        ImageArtifactType,
        materialization=TerminalMaterializationSpec(
            ImageFileOptions(filename_suffix=".tif")
        ),
    )
    exported = ArtifactSpec.output(
        "Saved",
        ImageArtifactType,
        materialization=MaterializationSpec(ImageFileOptions(filename_suffix=".npy")),
    )

    expectation = RuntimeExportExpectation.from_output_specs((terminal, exported))

    assert expectation.output_specs == (exported,)


def test_scalar_image_materialization_preserves_planned_vfs_path() -> None:
    filemanager = FileManager({"memory": MemoryStorageBackend()})
    spec = MaterializationSpec(ImageFileOptions(filename_suffix=".tif"))

    primary_path = materialize(
        spec,
        data=np.zeros((4, 5), dtype=np.uint16),
        path="/output/A01_s001_w1_z001_t001.tif",
        filemanager=filemanager,
        backends=("memory",), output_plan=materialization_output_plan()
    )

    assert primary_path == "/output/A01_s001_w1_z001_t001.tif"
    assert filemanager.exists(primary_path, "memory")
