"""DTO exports for the headless OpenHCS agent API.

The re-export surface is lazy: importing one concrete DTO submodule, such as
``openhcs.agent.dto.common``, must not import the full agent DTO graph.
"""

from python_introspect import lazy_exports

__all__ = lazy_exports(
    globals(),
    {
        "openhcs.agent.dto.common": (
            "SCHEMA_VERSION",
            "RenderedSource",
        ),
        "openhcs.agent.dto.mcp": (
            "McpServerHealthResult",
        ),
        "openhcs.agent.dto.authoring": (
            "AuthoringContext",
            "AuthoringContextRequest",
        ),
        "openhcs.agent.dto.architecture": (
            "ArchitectureTopic",
            "ArchitectureTopicPage",
            "ArchitectureTopicSummary",
            "InternalApiSymbol",
        ),
        "openhcs.agent.dto.config": (
            "ConfigFieldSchema",
            "ConfigPatch",
            "ConfigRegisteredType",
            "ConfigRef",
            "ConfigRegistrySchema",
            "ConfigSchema",
            "ConfigSchemaRequest",
            "ConfigSourceRenderRequest",
            "ConfigTypeSchema",
            "ConfigValidationResult",
        ),
        "openhcs.agent.dto.functions": (
            "CellProfilerArtifactBindingSummary",
            "CellProfilerModuleDeclarationSummary",
            "CustomFunctionRegistrationRequest",
            "CustomFunctionRegistrationResult",
            "FunctionDetailRequest",
            "FunctionArtifactSpec",
            "FunctionCatalogEntry",
            "FunctionCatalogPage",
            "FunctionDetail",
            "FunctionSearchRequest",
            "FunctionParameterSource",
            "FunctionParameterSpec",
            "FunctionRuntimeContractSummary",
        ),
        "openhcs.agent.dto.knowledge": (
            "KnowledgeBaseCatalog",
            "KnowledgeBaseDocument",
            "KnowledgeBaseDocumentRequest",
            "KnowledgeBaseDocumentSourceProjection",
            "KnowledgeBaseDocumentSummary",
            "KnowledgeBaseSearchHit",
            "KnowledgeBaseSearchRequest",
            "KnowledgeBaseSearchResult",
            "KnowledgeBaseSectionSummary",
        ),
        "openhcs.agent.dto.execution": (
            "ArtifactInputPlanSummary",
            "ArtifactMaterializationPathSummary",
            "ArtifactMaterializationPlanSummary",
            "ArtifactPlanInspection",
            "ArtifactPlanSummary",
            "ArtifactStoragePlanSummary",
            "CompiledStepPlanSummary",
            "MainFlowMaterializationPlanSummary",
            "PipelineSourceArtifactPlanInspectionRequest",
            "RuntimeDebugInspectionRequest",
            "RuntimeDebugInspectionResult",
            "RuntimeExecutionStatus",
            "RuntimeServerExecutionStatusRequest",
            "RuntimeServerInfo",
            "RuntimeServerInfoRequest",
            "RuntimeServerScanRequest",
            "RuntimeServerScanResult",
            "SourceWorkspaceFileRecord",
            "SourceWorkspaceSummary",
            "ViewerStreamingPlanSummary",
        ),
        "openhcs.agent.dto.execution_connection": (
            "ExecutionConnectionSpec",
        ),
        "openhcs.agent.dto.pipeline": (
            "CreatePipelineRequest",
            "FunctionSpecRef",
            "FunctionStepAddRequest",
            "FunctionStepSpec",
            "PipelineRef",
            "PipelineSourceRenderRequest",
            "PipelineSpec",
            "PipelineValidationRequest",
            "PipelineValidationResult",
        ),
        "openhcs.agent.dto.plate": (
            "PlateFileQueryRecordSummary",
            "PlateFileQueryRequest",
            "PlateFileQueryResult",
            "PlateFileStreamRequest",
            "PlateFileStreamResult",
            "PlateInspectionBounds",
            "PlateInspectionComponentSummary",
            "PlateInspectionComponentValue",
            "PlateInspectionConfidence",
            "PlateInspectionHandlerCandidate",
            "PlateInspectionImageFileSummary",
            "PlateInspectionImageRecordSummary",
            "PlateInspectionIngestionRoute",
            "PlateInspectionIssueCode",
            "PlateInspectionParseFailure",
            "PlateInspectionParseSummary",
            "PlateInspectionResultFileRecordSummary",
            "PlateInspectionResultFileSummary",
            "PlateInspectionStatus",
            "PlateInspectionSourceBindingRole",
            "PlateInspectionValueSource",
            "PlateInspectionWorkflowAdvice",
            "PlateInspectionWorkflowScope",
            "PlateInspectionWorkspacePreparation",
            "PlateImageSampleRequest",
            "PlateImageSampleResult",
            "PlatePathInspectionRequest",
            "PlatePathInspectionResult",
            "PlateWorkspacePreparationOperation",
            "SelectedPlateFileQueryTarget",
            "SelectedPlateFileQueryRequest",
            "SelectedPlateFileQueryResult",
            "SelectedPlateFileStreamRequest",
            "SelectedPlateFileStreamResult",
            "SelectedPlateImageInspectionRequest",
            "SelectedPlateImageInspectionResult",
            "SelectedPlateImageSampleRequest",
            "SelectedPlateImageSampleResult",
            "SyntheticPlateGenerationRequest",
            "SyntheticPlateGenerationResult",
        ),
        "openhcs.agent.dto.viewer": (
            "ViewerWindowDescriptor",
            "ViewerWindowLayerPayloads",
            "ViewerWindowLayerState",
            "ViewerWindowLayerValidationSummary",
            "ViewerWindowLayerIsolationRequest",
            "ViewerWindowLayerIsolationResult",
            "ViewerWindowLayerRetirementRequest",
            "ViewerWindowLayerRetirementResult",
            "ViewerWindowLayerVisibilityRecord",
            "ViewerWindowImageSampleRequest",
            "ViewerWindowImageSampleResult",
            "ViewerWindowNavigationRequest",
            "ViewerWindowNavigationResult",
            "ViewerWindowPayloadRecord",
            "ViewerWindowPayloadRequest",
            "ViewerWindowPayloadResult",
            "ViewerWindowProbeResult",
            "ViewerWindowRoiSummaryRequest",
            "ViewerWindowRoiSummaryResult",
            "ViewerWindowSnapshotRequest",
            "ViewerWindowSnapshotResult",
            "ViewerWindowStateRequest",
            "ViewerWindowStateResult",
            "ViewerWindowValidationPolicy",
            "ViewerWindowValidationRequest",
            "ViewerWindowValidationSummaryResult",
        ),
        "openhcs.agent.dto.ui_bridge": (
            "UiPlateManagerState",
            "UiSelectedPlateWorkflowKind",
            "UiSelectedPlateWorkflowRequest",
            "UiSelectedPlateWorkflowResult",
        ),
    },
)


def _dto_wire_value(value: object) -> object:
    """Convert one field value to its JSON-serializable wire form.

    Handles the common DTO transforms: Enum -> value, tuple -> list,
    ComponentFilters -> mapping, None passthrough, and to_jsonable fallback.
    """
    if value is None:
        return None
    if isinstance(value, str):
        return value
    if isinstance(value, (int, float, bool)):
        return value
    if isinstance(value, Enum):
        return value.value
    if isinstance(value, tuple):
        return [_dto_wire_value(v) for v in value]
    if isinstance(value, dict):
        return {k: _dto_wire_value(v) for k, v in value.items()}
    if isinstance(value, Mapping):
        return {k: _dto_wire_value(v) for k, v in value.items()}
    if hasattr(value, "as_mapping"):
        return value.as_mapping()
    if hasattr(value, "to_jsonable"):
        return value.to_jsonable()
    from python_introspect import to_jsonable
    return to_jsonable(value)


from collections.abc import Mapping
from enum import Enum
