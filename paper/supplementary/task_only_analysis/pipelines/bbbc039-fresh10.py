from pathlib import Path
from dataclasses import replace
from openhcs.core.source_bindings import ImportedMetadataJoin
import sys
sys.path.insert(0, "/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc039-preparation-20261002/BBBC039/input")
from source_bindings import source_bindings_config
from openhcs.constants.constants import GroupBy, Microscope
from openhcs.constants.input_source import InputSource
from openhcs.core.config import (PipelineConfig, LazyProcessingConfig, LazySourceBindingsConfig, LazyPathPlanningConfig, LazyAnalysisConsolidationConfig)
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.func_registry import get_function
from openhcs.processing.backends.cellprofiler.primary_objects import UnclumpMethod, WatershedMethod
from openhcs.processing.backends.cellprofiler.morphology import FillHolesOption
from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerThresholdScope, CellProfilerThresholdMethod
from openhcs.processing.backends.cellprofiler.object_images import ImageMode

pipeline_config = PipelineConfig(
    microscope=Microscope.SOURCE_BINDINGS,
    num_workers=2,
    processing_config=LazyProcessingConfig(variable_components=[], group_by=GroupBy.NONE, input_source=InputSource.PREVIOUS_STEP),
    source_bindings_config=LazySourceBindingsConfig(
        metadata_rules=source_bindings_config.metadata_rules,
        source_filters=source_bindings_config.source_filters,
        bindings=source_bindings_config.bindings,
        imported_metadata_tables=tuple(replace(table, joins=table.joins + (ImportedMetadataJoin(image_metadata_field="plate", imported_metadata_field="plate"),)) for table in source_bindings_config.imported_metadata_tables),
        grouping_metadata_fields=source_bindings_config.grouping_metadata_fields),
    path_planning_config=LazyPathPlanningConfig(global_output_folder=Path("/run/media/ts/hdd/openhcs-science/next-h00488-h00389-bbbc03996-fresh10-after-capacity-20261005/BBBC039_FRESH10_COVERAGE_96/attempts/FULL200"), output_dir_suffix="_FULL200"),
    analysis_consolidation_config=LazyAnalysisConsolidationConfig(enabled=True, metaxpress_style=False),
)
pipeline_steps = [
    FunctionStep(
        name="IdentifyDNAInstances",
        func=(get_function("openhcs:cellprofiler_identify_primary_objects"), {
            "select_the_input_image": "dna",
            "name_the_primary_objects_to_be_identified": "Nuclei",
            "min_diameter": 12, "max_diameter": 80,
            "exclude_size": True, "exclude_border_objects": False,
            "unclump_method": UnclumpMethod.SHAPE,
            "watershed_method": WatershedMethod.SHAPE,
            "automatic_suppression": False, "maxima_suppression_size": 12.0,
            "low_res_maxima": False,
            "fill_holes": FillHolesOption.AFTER_DECLUMP,
            "use_advanced_settings": True,
            "threshold_scope": CellProfilerThresholdScope.GLOBAL,
            "threshold_method": CellProfilerThresholdMethod.MINIMUM_CROSS_ENTROPY,
            "threshold_correction_factor": 1.0,
            "threshold_min": 0.0, "threshold_max": 1.0,
            "threshold_smoothing_scale": 1.3488,
        }),
        processing_config=LazyProcessingConfig(input_source=InputSource.PIPELINE_START)),
    FunctionStep(name="ExportObjectTables",
        func=(get_function("openhcs:cellprofiler_export_to_spreadsheet"), {
            "add_filename_prefix": False, "add_image_metadata": True,
            "add_image_file_names": True,
        }),
        processing_config=LazyProcessingConfig(variable_components=[], group_by=GroupBy.NONE)),
]

