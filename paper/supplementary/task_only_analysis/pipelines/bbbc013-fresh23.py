# Derived OpenHCS source-binding declaration

from openhcs.constants.constants import AllComponents
from openhcs.core.config import LazySourceBindingsConfig
from openhcs.core.source_bindings import (
    ComponentSelector,
    ImportedMetadataJoin,
    ImportedMetadataTable,
    MetadataExtractionRule,
    MetadataSelector,
    MetadataSource,
    NamedSourceBinding,
    SourceBindingMatchDimension,
    SourceBindingMatchField,
    SourceBindingMatchMethod,
    SourceBindingMatchPlan,
    SourceBindingOrigin,
    SourceBindingsConfig,
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
    SourceSelector,
)

source_bindings_config = LazySourceBindingsConfig(
    metadata_rules=(
        MetadataExtractionRule(
            source=MetadataSource.FILE_NAME,
            pattern='^(?:plate-(?P<plate>[^_]+)_)?well-(?P<well>[A-P]\\d{2})_site-(?P<site>[^_]+)_channel-(?P<channel>[^.]+)\\.(?:tif|tiff|bmp|png)$'
        ),
    ),
    match_plan=SourceBindingMatchPlan(
        method=SourceBindingMatchMethod.METADATA,
        dimensions=(
            SourceBindingMatchDimension(
                fields=(
                    SourceBindingMatchField(
                        alias='gfp',
                        metadata_field='well'
                    ),
                    SourceBindingMatchField(
                        alias='dna',
                        metadata_field='well'
                    )
                )
            ),
            SourceBindingMatchDimension(
                fields=(
                    SourceBindingMatchField(
                        alias='gfp',
                        metadata_field='site'
                    ),
                    SourceBindingMatchField(
                        alias='dna',
                        metadata_field='site'
                    )
                )
            )
        )
    ),
    source_filters=(
        SourceFilterClause(
            subject=SourceFilterSubject.FILE,
            match_type=SourceFilterMatchType.IS_IMAGE
        ),
    ),
    bindings=(
        NamedSourceBinding(
            alias='gfp',
            selector=SourceSelector(
                metadata=(
                    MetadataSelector(
                        field='channel',
                        value='GFP'
                    ),
                )
            ),
            origin=SourceBindingOrigin.PIPELINE_START,
            load_as_monochrome=True,
            component_identity=(
                ComponentSelector(
                    component=AllComponents.CHANNEL,
                    value='GFP'
                ),
            )
        ),
        NamedSourceBinding(
            alias='dna',
            selector=SourceSelector(
                metadata=(
                    MetadataSelector(
                        field='channel',
                        value='DNA'
                    ),
                )
            ),
            origin=SourceBindingOrigin.PIPELINE_START,
            load_as_monochrome=True,
            component_identity=(
                ComponentSelector(
                    component=AllComponents.CHANNEL,
                    value='DNA'
                ),
            )
        )
    ),
    imported_metadata_tables=(
        ImportedMetadataTable(
            location='/run/media/ts/hdd/openhcs-science/next-bbbc013-retina-fresh23-after-terminals-20261006/BBBC013_FRESH23_96/input-workspace/source_sets.csv',
            joins=(
                ImportedMetadataJoin(
                    image_metadata_field='well',
                    imported_metadata_field='well'
                ),
                ImportedMetadataJoin(
                    image_metadata_field='site',
                    imported_metadata_field='site'
                )
            )
        ),
    ),
    grouping_metadata_fields=(
        'well',
    )
)

from pathlib import Path
from openhcs.constants.constants import GroupBy, VariableComponents, Microscope
from openhcs.constants.input_source import InputSource
from openhcs.core.config import LazySourceBindingsConfig, PipelineConfig, LazyProcessingConfig, LazyPathPlanningConfig, LazyWellFilterConfig, LazyNapariStreamingConfig, NapariDimensionMode, LazyStepMaterializationConfig
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.func_registry import get_function
from openhcs.processing.backends.cellprofiler.intensity import RescaleMethod
from zmqruntime.config import TransportMode

pipeline_config = PipelineConfig(
    microscope=Microscope.SOURCE_BINDINGS,
    num_workers=2, use_threading=True, materialize_runtime_artifacts=True,
    source_bindings_config=source_bindings_config,
    well_filter_config=LazyWellFilterConfig(well_filter=None),
    processing_config=LazyProcessingConfig(variable_components=[VariableComponents.SITE], group_by=GroupBy.CHANNEL, input_source=InputSource.PREVIOUS_STEP),
    path_planning_config=LazyPathPlanningConfig(global_output_folder=Path("/run/media/ts/hdd/openhcs-science/next-bbbc013-retina-fresh23-after-terminals-20261006/BBBC013_FRESH23_96/FULL_S08")),
    napari_streaming_config=LazyNapariStreamingConfig(enabled=False, port=6017, host="localhost", transport_mode=TransportMode.TCP, persistent=True, channel_mode=NapariDimensionMode.LAYER, well_mode=NapariDimensionMode.LAYER, well_filter=["A01","A02","A06","A12","C01","C07","D12","E01","E12","F06","H01","H11"]),
)

pipeline_steps = [
    FunctionStep(name="DNA codebook units", func=(get_function("openhcs:cellprofiler_rescale_intensity"), {"rescale_method": RescaleMethod.DIVIDE_BY_VALUE, "divisor_value":1.0, "select_the_input_image":"dna", "name_the_output_image":"dna_unit"}), processing_config=LazyProcessingConfig(input_source=InputSource.PIPELINE_START), napari_streaming_config=LazyNapariStreamingConfig(enabled=True), step_materialization_config=LazyStepMaterializationConfig(enabled=True)),
    FunctionStep(name="GFP codebook units", func=(get_function("openhcs:cellprofiler_rescale_intensity"), {"rescale_method": RescaleMethod.DIVIDE_BY_VALUE, "divisor_value":1.0, "select_the_input_image":"gfp", "name_the_output_image":"gfp_unit"}), processing_config=LazyProcessingConfig(input_source=InputSource.PIPELINE_START), napari_streaming_config=LazyNapariStreamingConfig(enabled=True), step_materialization_config=LazyStepMaterializationConfig(enabled=True)),
]

from openhcs.processing.backends.cellprofiler.primary_objects import UnclumpMethod
from openhcs.processing.backends.cellprofiler.primary_objects import WatershedMethod
from openhcs.processing.backends.cellprofiler.morphology import FillHolesOption
from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerThresholdScope
from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerThresholdMethod
from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerOtsuMethod
from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerThresholdAssignment
from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerAveragingMethod
from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerVarianceMethod
from openhcs.processing.backends.cellprofiler.primary_objects import ExcessObjectHandling
from openhcs.processing.backends.cellprofiler._backend import CellProfilerBackendProvider
from openhcs.processing.backends.cellprofiler.secondary import SecondaryMethod
from openhcs.processing.backends.cellprofiler.image_math import ImageMathOperation
from openhcs.processing.backends.cellprofiler.measurement_math import CalculateMathRoundingMethod
from openhcs.processing.backends.cellprofiler.spreadsheet_export import SpreadsheetDelimiter
from openhcs.processing.backends.cellprofiler.spreadsheet_export import SpreadsheetNanRepresentation
from openhcs.processing.backends.cellprofiler.object_images import ImageMode
from openhcs.processing.backends.cellprofiler.intensity import RescaleMethod
from openhcs.processing.backends.cellprofiler.intensity import AutomaticLow
from openhcs.processing.backends.cellprofiler.intensity import AutomaticHigh

def cpstep(name, fid, **kwargs):
    return FunctionStep(name=name, func=(get_function("openhcs:"+fid), kwargs), napari_streaming_config=LazyNapariStreamingConfig(enabled=name.startswith("Nuclei") or name.startswith("Cells")), step_materialization_config=LazyStepMaterializationConfig(enabled=name.startswith("Durable")))

pipeline_steps += [
    cpstep("Nuclei intensity markers", "cellprofiler_identify_primary_objects", select_the_input_image="dna_unit", name_the_primary_objects_to_be_identified="Nuclei", min_diameter=8, max_diameter=45, exclude_size=True, exclude_border_objects=True, unclump_method=UnclumpMethod.INTENSITY, automatic_smoothing=False, smoothing_filter_size=8, watershed_method=WatershedMethod.INTENSITY, automatic_suppression=False, maxima_suppression_size=5.0, low_res_maxima=False, fill_holes=FillHolesOption.AFTER_BOTH, threshold_method=CellProfilerThresholdMethod.MINIMUM_CROSS_ENTROPY, threshold_correction_factor=0.9, threshold_min=18/255, threshold_smoothing_scale=1.35),
    cpstep("Cells GFP propagation", "cellprofiler_identify_secondary_objects", select_the_input_image="gfp_unit", select_the_input_objects="Nuclei", name_the_objects_to_be_identified="Cells", method=SecondaryMethod.PROPAGATION, threshold_method=CellProfilerThresholdMethod.MINIMUM_CROSS_ENTROPY, threshold_correction_factor=0.45, threshold_smoothing_scale=1.0, threshold_min=2/255, regularization_factor=0.05, fill_holes=False, discard_edge_objects=False),
]

pipeline_steps += [
    cpstep("Cytoplasm exclude nuclei", "cellprofiler_identify_tertiary_objects", select_the_larger_identified_objects="Cells", select_the_smaller_identified_objects="Nuclei", name_the_tertiary_objects_to_be_identified="Cytoplasm", shrink_primary=False),
    cpstep("GFP compartment intensity", "cellprofiler_measure_object_intensity", select_images_to_measure=("gfp_unit",), select_object_sets_to_measure=("Nuclei", "Cytoplasm")),
    cpstep("Durable nucleus labels", "cellprofiler_convert_objects_to_image", select_the_input_objects="Nuclei", name_the_output_image="nucleus_labels", image_mode=ImageMode.UINT16),
    cpstep("Durable cell labels", "cellprofiler_convert_objects_to_image", select_the_input_objects="Cells", name_the_output_image="cell_labels", image_mode=ImageMode.UINT16),
    FunctionStep(name="Durable catalog tables", func=(get_function("openhcs:cellprofiler_export_to_spreadsheet"), {"add_image_metadata":True, "calculate_aggregate_means":False, "calculate_aggregate_medians":False, "calculate_aggregate_standard_deviations":False, "filename_prefix":"catalog_"})),
]

from openhcs.processing.custom_functions import bbbc013_compartment_qc_v4
pipeline_steps.insert(6, FunctionStep(name="Identity linked compartment QC", func={"GFP":(bbbc013_compartment_qc_v4,{"minimum_cytoplasm_pixels":20})}, processing_config=LazyProcessingConfig(input_source=InputSource.PIPELINE_START), step_materialization_config=LazyStepMaterializationConfig(enabled=False)))

from openhcs.processing.custom_functions import bbbc013_assay_statistics_v1, bbbc013_dose_response_v2
plate_design = (('A01', 'Wortmannin', 'negative_control', 0.0), ('A02', 'Wortmannin', 'empty', 0.0), ('A03', 'Wortmannin', 'dose', 0.98), ('A04', 'Wortmannin', 'dose', 1.95), ('A05', 'Wortmannin', 'dose', 3.91), ('A06', 'Wortmannin', 'dose', 7.81), ('A07', 'Wortmannin', 'dose', 15.63), ('A08', 'Wortmannin', 'dose', 31.25), ('A09', 'Wortmannin', 'dose', 62.5), ('A10', 'Wortmannin', 'dose', 125.0), ('A11', 'Wortmannin', 'dose', 250.0), ('A12', 'Wortmannin', 'positive_control', 150.0), ('B01', 'Wortmannin', 'negative_control', 0.0), ('B02', 'Wortmannin', 'empty', 0.0), ('B03', 'Wortmannin', 'dose', 0.98), ('B04', 'Wortmannin', 'dose', 1.95), ('B05', 'Wortmannin', 'dose', 3.91), ('B06', 'Wortmannin', 'dose', 7.81), ('B07', 'Wortmannin', 'dose', 15.63), ('B08', 'Wortmannin', 'dose', 31.25), ('B09', 'Wortmannin', 'dose', 62.5), ('B10', 'Wortmannin', 'dose', 125.0), ('B11', 'Wortmannin', 'dose', 250.0), ('B12', 'Wortmannin', 'positive_control', 150.0), ('C01', 'Wortmannin', 'negative_control', 0.0), ('C02', 'Wortmannin', 'empty', 0.0), ('C03', 'Wortmannin', 'dose', 0.98), ('C04', 'Wortmannin', 'dose', 1.95), ('C05', 'Wortmannin', 'dose', 3.91), ('C06', 'Wortmannin', 'dose', 7.81), ('C07', 'Wortmannin', 'dose', 15.63), ('C08', 'Wortmannin', 'dose', 31.25), ('C09', 'Wortmannin', 'dose', 62.5), ('C10', 'Wortmannin', 'dose', 125.0), ('C11', 'Wortmannin', 'dose', 250.0), ('C12', 'Wortmannin', 'positive_control', 150.0), ('D01', 'Wortmannin', 'negative_control', 0.0), ('D02', 'Wortmannin', 'empty', 0.0), ('D03', 'Wortmannin', 'dose', 0.98), ('D04', 'Wortmannin', 'dose', 1.95), ('D05', 'Wortmannin', 'dose', 3.91), ('D06', 'Wortmannin', 'dose', 7.81), ('D07', 'Wortmannin', 'dose', 15.63), ('D08', 'Wortmannin', 'dose', 31.25), ('D09', 'Wortmannin', 'dose', 62.5), ('D10', 'Wortmannin', 'dose', 125.0), ('D11', 'Wortmannin', 'dose', 250.0), ('D12', 'Wortmannin', 'positive_control', 150.0), ('E01', 'LY294002', 'positive_control', 150.0), ('E02', 'LY294002', 'empty', 0.0), ('E03', 'LY294002', 'dose', 0.31), ('E04', 'LY294002', 'dose', 0.63), ('E05', 'LY294002', 'dose', 1.25), ('E06', 'LY294002', 'dose', 2.5), ('E07', 'LY294002', 'dose', 5.0), ('E08', 'LY294002', 'dose', 10.0), ('E09', 'LY294002', 'dose', 20.0), ('E10', 'LY294002', 'dose', 40.0), ('E11', 'LY294002', 'dose', 80.0), ('E12', 'LY294002', 'negative_control', 0.0), ('F01', 'LY294002', 'positive_control', 150.0), ('F02', 'LY294002', 'empty', 0.0), ('F03', 'LY294002', 'dose', 0.31), ('F04', 'LY294002', 'dose', 0.63), ('F05', 'LY294002', 'dose', 1.25), ('F06', 'LY294002', 'dose', 2.5), ('F07', 'LY294002', 'dose', 5.0), ('F08', 'LY294002', 'dose', 10.0), ('F09', 'LY294002', 'dose', 20.0), ('F10', 'LY294002', 'dose', 40.0), ('F11', 'LY294002', 'dose', 80.0), ('F12', 'LY294002', 'negative_control', 0.0), ('G01', 'LY294002', 'positive_control', 150.0), ('G02', 'LY294002', 'empty', 0.0), ('G03', 'LY294002', 'dose', 0.31), ('G04', 'LY294002', 'dose', 0.63), ('G05', 'LY294002', 'dose', 1.25), ('G06', 'LY294002', 'dose', 2.5), ('G07', 'LY294002', 'dose', 5.0), ('G08', 'LY294002', 'dose', 10.0), ('G09', 'LY294002', 'dose', 20.0), ('G10', 'LY294002', 'dose', 40.0), ('G11', 'LY294002', 'dose', 80.0), ('G12', 'LY294002', 'negative_control', 0.0), ('H01', 'LY294002', 'positive_control', 150.0), ('H02', 'LY294002', 'empty', 0.0), ('H03', 'LY294002', 'dose', 0.31), ('H04', 'LY294002', 'dose', 0.63), ('H05', 'LY294002', 'dose', 1.25), ('H06', 'LY294002', 'dose', 2.5), ('H07', 'LY294002', 'dose', 5.0), ('H08', 'LY294002', 'dose', 10.0), ('H09', 'LY294002', 'dose', 20.0), ('H10', 'LY294002', 'dose', 40.0), ('H11', 'LY294002', 'dose', 80.0), ('H12', 'LY294002', 'negative_control', 0.0))
source_metadata = (('A01', 'nM', 'vehicle'), ('A02', 'nM', 'Wortmannin'), ('A03', 'nM', 'Wortmannin'), ('A04', 'nM', 'Wortmannin'), ('A05', 'nM', 'Wortmannin'), ('A06', 'nM', 'Wortmannin'), ('A07', 'nM', 'Wortmannin'), ('A08', 'nM', 'Wortmannin'), ('A09', 'nM', 'Wortmannin'), ('A10', 'nM', 'Wortmannin'), ('A11', 'nM', 'Wortmannin'), ('A12', 'nM', 'Wortmannin'), ('B01', 'nM', 'vehicle'), ('B02', 'nM', 'Wortmannin'), ('B03', 'nM', 'Wortmannin'), ('B04', 'nM', 'Wortmannin'), ('B05', 'nM', 'Wortmannin'), ('B06', 'nM', 'Wortmannin'), ('B07', 'nM', 'Wortmannin'), ('B08', 'nM', 'Wortmannin'), ('B09', 'nM', 'Wortmannin'), ('B10', 'nM', 'Wortmannin'), ('B11', 'nM', 'Wortmannin'), ('B12', 'nM', 'Wortmannin'), ('C01', 'nM', 'vehicle'), ('C02', 'nM', 'Wortmannin'), ('C03', 'nM', 'Wortmannin'), ('C04', 'nM', 'Wortmannin'), ('C05', 'nM', 'Wortmannin'), ('C06', 'nM', 'Wortmannin'), ('C07', 'nM', 'Wortmannin'), ('C08', 'nM', 'Wortmannin'), ('C09', 'nM', 'Wortmannin'), ('C10', 'nM', 'Wortmannin'), ('C11', 'nM', 'Wortmannin'), ('C12', 'nM', 'Wortmannin'), ('D01', 'nM', 'vehicle'), ('D02', 'nM', 'Wortmannin'), ('D03', 'nM', 'Wortmannin'), ('D04', 'nM', 'Wortmannin'), ('D05', 'nM', 'Wortmannin'), ('D06', 'nM', 'Wortmannin'), ('D07', 'nM', 'Wortmannin'), ('D08', 'nM', 'Wortmannin'), ('D09', 'nM', 'Wortmannin'), ('D10', 'nM', 'Wortmannin'), ('D11', 'nM', 'Wortmannin'), ('D12', 'nM', 'Wortmannin'), ('E01', 'nM', 'Wortmannin'), ('E02', 'uM', 'LY294002'), ('E03', 'uM', 'LY294002'), ('E04', 'uM', 'LY294002'), ('E05', 'uM', 'LY294002'), ('E06', 'uM', 'LY294002'), ('E07', 'uM', 'LY294002'), ('E08', 'uM', 'LY294002'), ('E09', 'uM', 'LY294002'), ('E10', 'uM', 'LY294002'), ('E11', 'uM', 'LY294002'), ('E12', 'uM', 'vehicle'), ('F01', 'nM', 'Wortmannin'), ('F02', 'uM', 'LY294002'), ('F03', 'uM', 'LY294002'), ('F04', 'uM', 'LY294002'), ('F05', 'uM', 'LY294002'), ('F06', 'uM', 'LY294002'), ('F07', 'uM', 'LY294002'), ('F08', 'uM', 'LY294002'), ('F09', 'uM', 'LY294002'), ('F10', 'uM', 'LY294002'), ('F11', 'uM', 'LY294002'), ('F12', 'uM', 'vehicle'), ('G01', 'nM', 'Wortmannin'), ('G02', 'uM', 'LY294002'), ('G03', 'uM', 'LY294002'), ('G04', 'uM', 'LY294002'), ('G05', 'uM', 'LY294002'), ('G06', 'uM', 'LY294002'), ('G07', 'uM', 'LY294002'), ('G08', 'uM', 'LY294002'), ('G09', 'uM', 'LY294002'), ('G10', 'uM', 'LY294002'), ('G11', 'uM', 'LY294002'), ('G12', 'uM', 'vehicle'), ('H01', 'nM', 'Wortmannin'), ('H02', 'uM', 'LY294002'), ('H03', 'uM', 'LY294002'), ('H04', 'uM', 'LY294002'), ('H05', 'uM', 'LY294002'), ('H06', 'uM', 'LY294002'), ('H07', 'uM', 'LY294002'), ('H08', 'uM', 'LY294002'), ('H09', 'uM', 'LY294002'), ('H10', 'uM', 'LY294002'), ('H11', 'uM', 'LY294002'), ('H12', 'uM', 'vehicle'))
pipeline_steps += [
    FunctionStep(name="Plate assay statistics", func=(bbbc013_assay_statistics_v1, {"plate_design":plate_design})),
    FunctionStep(name="Plate dose response", func=(bbbc013_dose_response_v2, {"plate_design":plate_design,"source_metadata":source_metadata})),
]
