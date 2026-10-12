"""E1 guards: our code does not dispatch on Enum members outside listed boundaries.

A kind is a family whose members carry their behaviour (rule 1a). An ``Enum``
stays only as a boundary spelling: an external contract's literal table (a
CellProfiler setting, a Qt/OS/MCP name) or a processing function's parameter
choices. Dispatching on its members (``is``/``==``/``in`` against a member, a
``match`` case, a dict keyed by members, an ``EnumKeyedStrategyMixin`` key) is
allowed only where the table below lists the enum and module, with its reason.
Entries leave the table when their enum is converted; a stale entry fails.
"""

from __future__ import annotations

import ast
import re
from collections import defaultdict
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OPENHCS = ROOT / "openhcs"
ENUM_BASES = {"Enum", "IntEnum", "StrEnum", "Flag", "IntFlag"}

PROCESSING_FUNCTIONS = "openhcs/processing/backends/"
"""Processing function modules: an enum declared here is a function's parameter
choice list (most spell a CellProfiler setting), dispatched only by that
function's module and its backend twins."""

CELLPROFILER_SPELLING = "CellProfiler setting or column literal table"

ALLOWED: dict[tuple[str, str], str] = {
    ('CPAPropertyName', 'openhcs/interop/cellprofiler/analyst_export.py'): CELLPROFILER_SPELLING,
    ('CapabilityKind', 'openhcs/agent/capabilities.py'): 'U2: MCP tool-input filter choices; needs the MCP binder to project family fields (python-introspect 0.2.8)',
    ('CapabilityRole', 'openhcs/agent/capabilities.py'): 'U2: MCP tool-input filter choices; needs the MCP binder to project family fields (python-introspect 0.2.8)',
    ('CapabilityVisibility', 'openhcs/agent/capabilities.py'): 'U2: MCP tool-input filter choices; needs the MCP binder to project family fields (python-introspect 0.2.8)',
    ('CellProfilerMeasurementTargetScope', 'openhcs/interop/cellprofiler/measurement_scope.py'): CELLPROFILER_SPELLING,
    ('CellProfilerMeasurementTargetScope', 'openhcs/interop/cellprofiler/module_artifact_declarations.py'): CELLPROFILER_SPELLING,
    ('CellProfilerObjectTableMode', 'openhcs/interop/cellprofiler/analyst_export.py'): CELLPROFILER_SPELLING,
    ('CellProfilerSourceImageProjectionField', 'openhcs/interop/cellprofiler/analyst_export.py'): CELLPROFILER_SPELLING,
    ('FunctionStepExecutionScope', 'openhcs/core/artifacts/input_projection.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('FunctionStepExecutionScope', 'openhcs/core/callable_contract.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('FunctionStepExecutionScope', 'openhcs/core/function_patterns.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('FunctionStepExecutionScope', 'openhcs/core/function_reference.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('FunctionStepExecutionScope', 'openhcs/core/orchestrator/bundle_execution.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('FunctionStepExecutionScope', 'openhcs/core/orchestrator/worker_execution.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('FunctionStepExecutionScope', 'openhcs/core/pipeline/artifact_planning.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('FunctionStepExecutionScope', 'openhcs/core/pipeline/compilation_session.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('FunctionStepExecutionScope', 'openhcs/core/pipeline/compiler.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('FunctionStepExecutionScope', 'openhcs/core/pipeline/funcstep_contract_validator.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('FunctionStepExecutionScope', 'openhcs/core/pipeline/path_planner.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('FunctionStepExecutionScope', 'openhcs/interop/cellprofiler/compile_time_contracts.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('FunctionStepExecutionScope', 'openhcs/interop/cellprofiler/module_callable_abi.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('FunctionStepExecutionScope', 'openhcs/interop/cellprofiler/module_declarations.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('FunctionStepExecutionScope', 'openhcs/processing/backends/lib_registry/openhcs_registry.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('FunctionStepExecutionScope', 'openhcs/processing/backends/lib_registry/unified_registry.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('FunctionStepExecutionScope', 'openhcs/processing/custom_functions/validation.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('ImagePayloadConsumption', 'openhcs/core/callable_contract.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('ImagePayloadConsumption', 'openhcs/core/function_patterns.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('ImagePayloadConsumption', 'openhcs/core/steps/function_execution.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('ImagePayloadConsumption', 'openhcs/interop/cellprofiler/module_artifact_declarations.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('ImagePayloadConsumption', 'openhcs/interop/cellprofiler/runtime/module_execution.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('ImagePayloadMetadataCompositionMode', 'openhcs/core/aligned_image_payload.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('ImagePayloadMetadataCompositionMode', 'openhcs/core/runtime_image_values.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('ImagePayloadMetadataCompositionMode', 'openhcs/interop/cellprofiler/runtime/invocation.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('MainFlowInputProjection', 'openhcs/core/steps/function_runtime.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('MainFlowInputProjection', 'openhcs/interop/cellprofiler/runtime/artifact_binding.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('McpWireContentType', 'openhcs/mcp/dev_client_core.py'): 'MCP content-type names',
    ('McpWireMethod', 'openhcs/mcp/dev_client_core.py'): 'MCP JSON-RPC method names',
    ('MeasurementObjectRowIdentity', 'openhcs/interop/cellprofiler/runtime/object_measurement_row_policies.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/core/measurement_feature_queries.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/core/measurement_row_materialization.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/core/runtime_artifact_queries.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/core/runtime_spatial_grid.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/interop/cellprofiler/module_artifact_declarations.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/interop/cellprofiler/runtime/measurement_recording.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/interop/cellprofiler/runtime/measurement_rows.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/interop/cellprofiler/runtime/object_measurement_vectors.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/interop/cellprofiler/runtime/relationship_measurement_rows.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/processing/backends/cellprofiler/alignment.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/processing/backends/cellprofiler/classification.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/processing/backends/cellprofiler/colocalization.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/processing/backends/cellprofiler/flagging.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/processing/backends/cellprofiler/intensity.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/processing/backends/cellprofiler/intensity_distribution.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/processing/backends/cellprofiler/measurement_math.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/processing/backends/cellprofiler/neighbors.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/processing/backends/cellprofiler/relationships.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/processing/backends/cellprofiler/spreadsheet_export.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/processing/backends/cellprofiler/thresholding.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowAxisField', 'openhcs/processing/backends/cellprofiler/tracking.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowValueField', 'openhcs/interop/cellprofiler/runtime/measurement_rows.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementRowValueField', 'openhcs/processing/backends/cellprofiler/measurement_math.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementScope', 'openhcs/core/equivalence/keys.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementScope', 'openhcs/core/equivalence/measurement_features.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementScope', 'openhcs/core/measurement_row_materialization.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementScope', 'openhcs/core/runtime_artifact_queries.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementScope', 'openhcs/core/runtime_measurements.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementScope', 'openhcs/interop/cellprofiler/analyst_export.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementScope', 'openhcs/interop/cellprofiler/database_column_dialect.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementScope', 'openhcs/interop/cellprofiler/image_set_numbering.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementScope', 'openhcs/interop/cellprofiler/measurement_dialect.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementScope', 'openhcs/interop/cellprofiler/measurement_scope.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementScope', 'openhcs/interop/cellprofiler/module_measurement_features.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementScope', 'openhcs/processing/backends/cellprofiler/calculate_statistics.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementScope', 'openhcs/processing/backends/cellprofiler/image_quality.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementScope', 'openhcs/processing/backends/cellprofiler/spreadsheet_export.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementStatistic', 'openhcs/core/equivalence/keys.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementStatistic', 'openhcs/core/equivalence/measurement_features.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementStatistic', 'openhcs/core/runtime_measurements.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementStatistic', 'openhcs/interop/cellprofiler/module_measurement_features.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MeasurementTableRowLayout', 'openhcs/interop/cellprofiler/analyst_export.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MissingObjectMeasurementValuePolicy', 'openhcs/interop/cellprofiler/runtime/object_measurement_row_completion.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('MultiprocessingStartMethod', 'openhcs/core/orchestrator/worker_execution.py'): 'Python multiprocessing start-method names; a class-valued top-level GlobalPipelineConfig field does not reach lazy PipelineConfig (ObjectState, L6)',
    ('MultiprocessingStartMethod', 'openhcs/core/worker_start_policy.py'): 'Python multiprocessing start-method names; a class-valued top-level GlobalPipelineConfig field does not reach lazy PipelineConfig (ObjectState, L6)',
    ('ObjectLabelDomainScope', 'openhcs/core/measurement_image_alignment.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('ObjectLabelDomainScope', 'openhcs/core/pipeline/function_contracts.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('ObjectLabelDomainScope', 'openhcs/core/runtime_object_label_building.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('ObjectLabelDomainScope', 'openhcs/core/runtime_object_label_domains.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('ObjectLabelDomainScope', 'openhcs/core/runtime_object_labels.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('ObjectLabelDomainScope', 'openhcs/core/runtime_relationships.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('ObjectLabelDomainScope', 'openhcs/interop/cellprofiler/runtime/measurement_rows.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('ObjectLabelDomainScope', 'openhcs/interop/cellprofiler/runtime/object_measurement_row_completion.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('ObjectLabelDomainScope', 'openhcs/interop/cellprofiler/runtime/relationship_measurement_rows.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('ObjectLabelDomainScope', 'openhcs/processing/backends/cellprofiler/outlines.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('ObjectLabelDomainScope', 'openhcs/processing/backends/cellprofiler/relationships.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('ObjectLabelRepresentation', 'openhcs/core/runtime_object_label_aggregation.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('ObjectLabelRepresentation', 'openhcs/core/runtime_object_labels.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('ObjectLabelRepresentation', 'openhcs/processing/backends/cellprofiler/shape.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('PlateFileKind', 'openhcs/agent/services/plate_inspection_service.py'): "U2: MCP tool-input choice with an 'all' literal; needs the MCP binder to project family fields (python-introspect 0.2.8)",
    ('PlateFileKind', 'openhcs/agent/services/plate_streaming_service.py'): "U2: MCP tool-input choice with an 'all' literal; needs the MCP binder to project family fields (python-introspect 0.2.8)",
    ('PlateFileKind', 'openhcs/agent/services/selected_plate_service.py'): "U2: MCP tool-input choice with an 'all' literal; needs the MCP binder to project family fields (python-introspect 0.2.8)",
    ('PlateFileKind', 'openhcs/core/plate_image_inventory.py'): "U2: MCP tool-input choice with an 'all' literal; needs the MCP binder to project family fields (python-introspect 0.2.8)",
    ('PlateFileKind', 'openhcs/mcp/installed_demo.py'): "U2: MCP tool-input choice with an 'all' literal; needs the MCP binder to project family fields (python-introspect 0.2.8)",
    ('PlateFileKind', 'openhcs/pyqt_gui/widgets/image_browser.py'): "U2: MCP tool-input choice with an 'all' literal; needs the MCP binder to project family fields (python-introspect 0.2.8)",
    ('PlateInspectionIssueCode', 'openhcs/mcp/dev_client_renderers/plate.py'): 'AgentError.code spellings read by the client',
    ('QtPlatformName', 'openhcs/runtime/viewer_protocol.py'): 'Qt QPA plugin names (QT_QPA_PLATFORM)',
    ('RuntimeCellValueKind', 'openhcs/core/equivalence/cells.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('RuntimeCellValueKind', 'openhcs/core/equivalence/measurement_features.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('RuntimeInvocationDomain', 'openhcs/core/function_patterns.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('RuntimeInvocationDomain', 'openhcs/core/steps/function_execution.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('RuntimeInvocationDomain', 'openhcs/core/steps/function_runtime.py'): 'K5 callable contract (#1202 merged, still an enum); needs an owner',
    ('RuntimeMeasurementFeatureNameMode', 'openhcs/core/equivalence/keys.py'): 'K3 measurement vocabulary (#1199 merged, still an enum); needs an owner',
    ('RuntimePlaneAxis', 'openhcs/core/aligned_image_payload.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/core/artifacts/kinds.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/core/debug.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/core/image_payload_execution_mode.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/core/measurement_image_alignment.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/core/runtime_image_values.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/core/runtime_measurements.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/core/runtime_object_labels.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/core/runtime_plane_projection.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/core/runtime_slice_alignment.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/core/runtime_sparse_labels.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/core/runtime_tabular_values.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/core/steps/function_runtime.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/interop/cellprofiler/runtime/adapter.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/interop/cellprofiler/runtime/artifact_binding.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/interop/cellprofiler/runtime/object_measurement_row_completion.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/processing/backends/cellprofiler/area_occupied.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/processing/backends/cellprofiler/colocalization.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/processing/backends/cellprofiler/color.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/processing/backends/cellprofiler/image_math.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/processing/backends/cellprofiler/intensity.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('RuntimePlaneAxis', 'openhcs/processing/backends/cellprofiler/intensity_distribution.py'): 'plane-mode family (G3: unowned); now unblocked by K2 and K3',
    ('ViewerControlField', 'openhcs/agent/services/viewer_window_service.py'): 'L7/G6: viewer reply keys; typed reply records replace the dicts',
    ('ViewerControlField', 'openhcs/runtime/napari_viewer_server.py'): 'L7/G6: viewer reply keys; typed reply records replace the dicts',
    ('ViewerControlField', 'openhcs/runtime/viewer_control_actions.py'): 'L7/G6: viewer reply keys; typed reply records replace the dicts',
    ('ViewerDescriptorField', 'openhcs/runtime/napari_viewer_server.py'): 'L7/G6: viewer reply keys; typed reply records replace the dicts',
    ('ViewerIntensityWindowField', 'openhcs/runtime/napari_viewer_server.py'): 'L7/G6: viewer reply keys; typed reply records replace the dicts',
    ('ViewerLayerField', 'openhcs/runtime/napari_viewer_server.py'): 'L7/G6: viewer reply keys; typed reply records replace the dicts',
    ('ViewerPayloadField', 'openhcs/runtime/napari_viewer_server.py'): 'L7/G6: viewer reply keys; typed reply records replace the dicts',
    ('WriteMode', 'openhcs/serialization/pycodify_formatters.py'): 'K3 measurement writers restate it; unblocked now that #1199 merged',
}


@lru_cache(maxsize=1)
def _trees() -> dict[str, ast.Module]:
    return {
        path.relative_to(ROOT).as_posix(): ast.parse(path.read_text(encoding="utf-8"))
        for path in sorted(OPENHCS.rglob("*.py"))
    }


def _module_path(dotted: str) -> str | None:
    base = dotted.replace(".", "/")
    for candidate in (f"{base}.py", f"{base}/__init__.py"):
        if candidate in _trees():
            return candidate
    return None


def _absolute(module: str, node: ast.ImportFrom) -> str:
    if not node.level:
        return node.module or ""
    package = module.removesuffix(".py").split("/")[: -node.level]
    return ".".join([*package, *([node.module] if node.module else [])])


@lru_cache(maxsize=None)
def _bindings(module: str) -> dict[str, tuple[str, str]]:
    """Top-level and nested class names, and imported names, of one module.

    A class binds to (module, name); an import binds to (source module, name).
    """

    bound: dict[str, tuple[str, str]] = {}
    for node in ast.walk(_trees()[module]):
        if isinstance(node, ast.ClassDef):
            bound.setdefault(node.name, (module, node.name))
        elif isinstance(node, ast.ImportFrom):
            source = _module_path(_absolute(module, node))
            if source is None:
                continue
            for alias in node.names:
                bound.setdefault(alias.asname or alias.name, (source, alias.name))
    return bound


@lru_cache(maxsize=None)
def _class(module: str, name: str, depth: int = 0) -> tuple[str, str] | None:
    """The (module, class name) a name in ``module`` refers to, following imports."""

    target = _bindings(module).get(name)
    if target is None or depth > 8:
        return None
    if target == (module, name):
        return target
    return _class(*target, depth + 1)


@lru_cache(maxsize=1)
def _enums() -> frozenset[tuple[str, str]]:
    """Every Enum class declared under openhcs/, as (module, name)."""

    declared: set[tuple[str, str]] = set()
    changed = True
    while changed:
        changed = False
        for module, tree in _trees().items():
            for node in ast.walk(tree):
                if not isinstance(node, ast.ClassDef) or (module, node.name) in declared:
                    continue
                for base in node.bases:
                    if isinstance(base, ast.Name | ast.Attribute):
                        name = base.id if isinstance(base, ast.Name) else base.attr
                        if name in ENUM_BASES or (
                            isinstance(base, ast.Name) and _class(module, name) in declared
                        ):
                            declared.add((module, node.name))
                            changed = True
                            break
    return frozenset(declared)


def _member_enum(node: ast.expr, module: str) -> str | None:
    """The enum a ``Enum.MEMBER`` (or ``.value``/``.name`` of one) expression names."""

    if isinstance(node, ast.Attribute) and node.attr in {"value", "name"}:
        node = node.value
    if not isinstance(node, ast.Attribute) or not node.attr.isupper():
        return None
    owner = node.value
    if isinstance(owner, ast.Name):
        found = _class(module, owner.id)
    elif isinstance(owner, ast.Attribute):
        found = next(
            (enum for enum in _enums() if enum[1] == owner.attr and enum[0] == module),
            None,
        )
    else:
        return None
    return found[1] if found in _enums() else None


@lru_cache(maxsize=1)
def enum_dispatch_sites() -> dict[tuple[str, str], list[int]]:
    """(enum name, module) -> lines where the module dispatches on its members."""

    sites: dict[tuple[str, str], list[int]] = defaultdict(list)
    compare_ops = (ast.Is, ast.IsNot, ast.Eq, ast.NotEq, ast.In, ast.NotIn)
    for module, tree in _trees().items():
        for node in ast.walk(tree):
            hits: list[str] = []
            if isinstance(node, ast.Compare) and any(
                isinstance(op, compare_ops) for op in node.ops
            ):
                for side in (node.left, *node.comparators):
                    candidates = (
                        side.elts if isinstance(side, ast.Tuple | ast.List | ast.Set)
                        else (side,)
                    )
                    hits.extend(
                        name
                        for candidate in candidates
                        if (name := _member_enum(candidate, module))
                    )
            elif isinstance(node, ast.match_case):
                hits.extend(
                    name
                    for pattern in ast.walk(node.pattern)
                    if isinstance(pattern, ast.MatchValue)
                    and (name := _member_enum(pattern.value, module))
                )
            elif isinstance(node, ast.Dict):
                hits.extend(
                    name
                    for key in node.keys
                    if key is not None and (name := _member_enum(key, module))
                )
            elif isinstance(node, ast.ClassDef):
                keyed = any(
                    "EnumKeyedStrategyMixin" in ast.unparse(base) for base in node.bases
                )
                for statement in node.body:
                    if not isinstance(statement, ast.Assign | ast.AnnAssign):
                        continue
                    if statement.value is None:
                        continue
                    targets = (
                        statement.targets
                        if isinstance(statement, ast.Assign)
                        else [statement.target]
                    )
                    names = [t.id for t in targets if isinstance(t, ast.Name)]
                    name = _member_enum(statement.value, module)
                    if name and (keyed or any("key" in target for target in names)):
                        hits.append(name)
            for name in hits:
                sites[(name, module)].append(getattr(node, "lineno", 0))
    return dict(sites)


def _allowed(enum_name: str, module: str) -> bool:
    if (enum_name, module) in ALLOWED:
        return True
    return module.startswith(PROCESSING_FUNCTIONS) and any(
        declaring.startswith(PROCESSING_FUNCTIONS)
        for declaring, name in _enums()
        if name == enum_name
    )


def test_enum_members_are_dispatched_only_at_listed_boundaries():
    offenders = sorted(
        f"{module}:{lines[0]} dispatches on {enum_name}"
        for (enum_name, module), lines in enum_dispatch_sites().items()
        if not _allowed(enum_name, module)
    )
    assert offenders == []


def test_boundary_table_only_lists_live_dispatch():
    stale = sorted(
        f"{enum_name} in {module}"
        for enum_name, module in ALLOWED
        if (enum_name, module) not in enum_dispatch_sites()
    )
    assert stale == []


DELETED_NAMES = (
    "SourceFilterMatcher",
    "SourceFilterTargetResolver",
    "SourceFilterMatchRequest",
    "metadata_source_texts",
    "filter_clause_matches",
    "rule_filters_match",
    "CellProfilerSourceFilterSubject",
    "CellProfilerSourceFilterOperator",
    "PipelineDebugSessionPhase",
    "PipelineDebugSessionContext",
    "PipelineDebugTargetState",
    "PipelineDebugPauseBoundaryState",
    "DebugSessionPhaseDeclarationBase",
    "DebugActionPlacement",
    "DebugToolbarAuxiliaryAction",
    "CompiledArtifactInspectionControlPayload",
    "ArtifactInspectionControlMessageType",
    "_jsonable_metadata_value",
    "_jsonable_array_values",
    "_jsonable_scalar",
    "_hashable_jsonable_metadata_value",
)
OLD_MEMBER_SPELLINGS = re.compile(
    r"\b(SourceFilterMatchType|SourceFilterSubject|MetadataSource|SourceSetRole"
    r"|SourceProjectionRole|SourceBindingOrigin)\.[A-Z_]+\b"
)
LIVE_TREES = ("openhcs", "tests", "scripts", "examples", "benchmark")


def _live_python_files():
    for tree in LIVE_TREES:
        for path in (ROOT / tree).rglob("*.py"):
            relative = path.relative_to(ROOT).as_posix()
            if relative.startswith("benchmark/results/") or path == Path(__file__):
                continue
            yield path


def test_deleted_names_and_enum_member_spellings_stay_deleted():
    names = re.compile(r"\b(" + "|".join(DELETED_NAMES) + r")\b")
    offenders = sorted(
        path.relative_to(ROOT).as_posix()
        for path in _live_python_files()
        if names.search(text := path.read_text(encoding="utf-8"))
        or OLD_MEMBER_SPELLINGS.search(text)
    )
    assert offenders == []


def test_source_family_kinds_are_not_enums():
    from enum import Enum

    from openhcs.core import debug_session_projection, source_bindings

    kinds = (
        source_bindings.SourceBindingOrigin,
        source_bindings.SourceSetRole,
        source_bindings.SourceProjectionRole,
        source_bindings.MetadataSource,
        source_bindings.SourceFilterSubject,
        source_bindings.SourceFilterMatchType,
        debug_session_projection.DebugSessionPhase,
    )
    assert not [kind for kind in kinds if issubclass(kind, Enum)]


DATASET_IDENTITY_MODULES = (
    "openhcs/core/source_projection.py",
    "openhcs/core/dataset_sources",
    "openhcs/microscopes/bioformats_adapter.py",
)


def test_dataset_and_store_identity_never_resolve_symlinks():
    offenders = sorted(
        f"{module}:{node.lineno}"
        for module, tree in _trees().items()
        if module.startswith(DATASET_IDENTITY_MODULES)
        for node in ast.walk(tree)
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "resolve"
        and not node.args
        and all(keyword.arg == "strict" for keyword in node.keywords)
    )
    assert offenders == []


def test_numpy_values_encode_through_to_jsonable():
    import numpy as np

    import openhcs.core.numpy_jsonable  # noqa: F401
    from python_introspect import to_jsonable

    assert to_jsonable(
        {"scalar": np.float32(1.5), "array": np.arange(4).reshape(2, 2), "n": np.int64(3)}
    ) == {"scalar": 1.5, "array": [[0, 1], [2, 3]], "n": 3}
