"""Capability registry for OpenHCS agent integrations."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Callable, Mapping
from dataclasses import MISSING, dataclass, field
from dataclasses import fields as dataclass_fields
from enum import Enum
from functools import cache
from importlib.metadata import distributions
from inspect import Parameter, getdoc
from inspect import signature as inspect_signature
from math import isfinite
from types import UnionType
from typing import (
    TYPE_CHECKING,
    ClassVar,
    Self,
    TypeAlias,
    get_args,
    get_type_hints,
)

from metaclass_registry import AutoRegisterMeta
from zmqruntime.client import EndpointShutdownResult

from openhcs.agent.services.execution_session_service import ExecutionSessionService

from openhcs.agent.dto.architecture import (
    ArchitectureTopic,
    ArchitectureTopicPage,
    InternalApiSymbol,
)
from openhcs.agent.dto.authoring import (
    AuthoringContext,
    AuthoringContextRequest,
)
from openhcs.agent.dto.common import (
    AGENT_PARAMETER_DESCRIPTION_METADATA_KEY,
    SCHEMA_VERSION,
    RenderedSource,
)
from openhcs.agent.dto.config import (
    ConfigPatch,
    ConfigRef,
    ConfigSchema,
    ConfigSchemaRequest,
    ConfigSourceRenderRequest,
    ConfigValidationResult,
)
from openhcs.agent.dto.execution import (
    ArtifactPlanInspection,
    CompileSubmissionRequest,
    ExecutionCancellationRequest,
    ExecutionJobCancellationResult,
    ExecutionJobRef,
    ExecutionJobStatus,
    ExecutionStatusRequest,
    OrchestratorSession,
    OrchestratorSessionCreationRequest,
    OrchestratorSessionRef,
    OrchestratorSessionRequest,
    PipelineExecutionSubmissionRequest,
    PipelineSourceArtifactPlanInspectionRequest,
    PipelineSourceOrchestratorSessionRequest,
    RuntimeDebugArtifactExportRequest,
    RuntimeDebugArtifactExportResult,
    RuntimeDebugCommandRequest,
    RuntimeDebugCommandResult,
    RuntimeDebugInspectionRequest,
    RuntimeDebugInspectionResult,
    RuntimeExecutionStatus,
    RuntimeServerExecutionStatusRequest,
    RuntimeServerInfo,
    RuntimeServerInfoRequest,
    RuntimeServerScanRequest,
    RuntimeServerScanResult,
    RuntimeBootstrapStartRequest,
    RuntimeBootstrapObserveRequest,
    RuntimeBootstrapState,
    RuntimeBootstrapCloseRequest,
    RuntimeBootstrapCloseResult,
    SourceWorkspaceSummary,
)
from openhcs.agent.dto.functions import (
    CustomFunctionRegistrationRequest,
    CustomFunctionRegistrationResult,
    CustomFunctionRegistrationHandle,
    CustomFunctionRegistrationObservation,
    FunctionCatalogPage,
    FunctionCatalogPreparationHandle,
    FunctionCatalogPreparationState,
    FunctionDetail,
    FunctionDetailRequest,
    FunctionSearchRequest,
)
from openhcs.agent.dto.knowledge import (
    KnowledgeBaseCatalog,
    KnowledgeBaseDocument,
    KnowledgeBaseDocumentRequest,
    KnowledgeBaseSearchRequest,
    KnowledgeBaseSearchResult,
)
from openhcs.agent.dto.mcp import McpServerHealthResult
from openhcs.agent.dto.pipeline import (
    CreatePipelineRequest,
    FunctionStepAddRequest,
    PipelineRef,
    PipelineSourceRenderRequest,
    PipelineSpec,
    PipelineValidationRequest,
    PipelineValidationResult,
)
from openhcs.agent.dto.plate import (
    PlateFileQueryRequest,
    PlateFileQueryResult,
    PlateFileStreamRequest,
    PlateFileStreamResult,
    PlateImageSampleRequest,
    PlateImageSampleResult,
    PlatePathInspectionRequest,
    PlatePathInspectionResult,
    SelectedPlateFileQueryRequest,
    SelectedPlateFileQueryResult,
    SelectedPlateFileStreamRequest,
    SelectedPlateFileStreamResult,
    SelectedPlateImageInspectionRequest,
    SelectedPlateImageInspectionResult,
    SelectedPlateImageSampleRequest,
    SelectedPlateImageSampleResult,
    SyntheticPlateGenerationRequest,
    SyntheticPlateGenerationResult,
)
from openhcs.agent.dto.ui_bridge import (
    UiActionCatalog,
    UiActionInvokeRequest,
    UiActionInvokeResult,
    UiBranchCatalog,
    UiBranchSwitchRequest,
    UiBridgeCatalog,
    UiBridgeOperationRef,
    UiBridgeOperationWaitRequest,
    UiBridgeStatus,
    UiCodeDocument,
    UiCodeDocumentApplyRequest,
    UiCodeDocumentApplyResult,
    UiCodeDocumentCatalog,
    UiCodeDocumentRequest,
    UiCodeDocumentValidationRequest,
    UiCodeDocumentValidationResult,
    UiObjectStateFieldHelpQuery,
    UiObjectStateFieldHelpResult,
    UiObjectStateFieldListQuery,
    UiObjectStateFieldListResult,
    UiObjectStateFieldMutationRequest,
    UiObjectStateFieldMutationResult,
    UiObjectStateScopeCatalog,
    UiObjectStateScopeListRequest,
    UiSelectedPlateWorkflowRequest,
    UiSelectedPlateWorkflowResult,
    UiSnapshotCatalog,
    UiSnapshotListRequest,
    UiSnapshotRestoreRequest,
    UiSnapshotRestoreResult,
    UiStateSurfaceCatalog,
    UiStateSurfaceDocument,
    UiStateSurfaceRequest,
    UiTimeTravelHeadRequest,
    UiWidgetActionInvokeRequest,
    UiWidgetActionInvokeResult,
    UiWidgetTreeRequest,
    UiWidgetTreeResult,
    UiWindowCatalog,
    UiWindowCloseRequest,
    UiWindowCloseResult,
    UiWindowFocusRequest,
    UiWindowFocusResult,
    UiWindowNavigateRequest,
    UiWindowNavigateResult,
    UiWindowSnapshotRequest,
    UiWindowSnapshotResult,
)
from openhcs.agent.dto.viewer import (
    ViewerWindowPolylineMeasurementRequest,
    ViewerWindowPolylineMeasurementResult,
    ViewerWindowRegionMeasurementRequest,
    ViewerWindowRegionMeasurementResult,
    ViewerEndpointDiscoveryResult,
    ViewerWindowCloseRequest,
    ViewerWindowImageIntensityRequest,
    ViewerWindowImageIntensityResult,
    ViewerWindowImageSampleRequest,
    ViewerWindowImageSampleResult,
    ViewerWindowIntensityWindowRequest,
    ViewerWindowIntensityWindowResult,
    ViewerWindowLayerIsolationRequest,
    ViewerWindowLayerIsolationResult,
    ViewerWindowLayerRetirementRequest,
    ViewerWindowLayerRetirementResult,
    ViewerWindowNavigationRequest,
    ViewerWindowNavigationResult,
    ViewerWindowPayloadRequest,
    ViewerWindowPayloadResult,
    ViewerWindowProbeResult,
    ViewerWindowRoiSummaryRequest,
    ViewerWindowRoiSummaryResult,
    ViewerWindowSnapshotRequest,
    ViewerWindowSnapshotResult,
    ViewerWindowStateRequest,
    ViewerWindowStateResult,
    ViewerWindowValidationRequest,
    ViewerWindowValidationSummaryResult,
    ViewerWindowViewportRequest,
    ViewerWindowViewportResult,
    ViewerWindowControlRequest,
    ViewerWindowImageColorRequest,
    ViewerWindowImageColorResult,
    ViewerWindowNativePresentationRequest,
    ViewerWindowNativePresentationResult,
)
from openhcs.runtime.viewer_controls import ViewerNavigationControlOptions
from python_introspect import to_jsonable

if TYPE_CHECKING:
    from argparse import ArgumentParser, Namespace

    from openhcs.mcp.dev_client_commanding import McpDevCliProjection
    from openhcs.mcp.server import McpCapabilityBinder


class CapabilityKind(Enum):
    RESOURCE = "resource"
    TOOL = "tool"
    PROMPT = "prompt"


class CapabilityTransportSemanticsABC(ABC):
    """Nominal owner of one MCP transport's server-facing semantics."""

    @abstractmethod
    def server_instructions(self) -> str:
        """Render instructions for the capability surface exposed here."""
        raise NotImplementedError


class LocalStdioCapabilityTransportSemantics(CapabilityTransportSemanticsABC):
    """Instructions for a local agent controlling the desktop and local runtime."""

    def server_instructions(self) -> str:
        from openhcs.agent.authoring_contexts import AuthoringContextDeclaration

        authoring_context_kinds = ", ".join(
            AuthoringContextDeclaration.allowed_values()
        )
        return (
            "OpenHCS tools inspect, author, compile, execute, and validate high-content "
            "microscopy workflows. "
            f"Call {agent_capabilities.health_check.name} first. If OpenHCS is unfamiliar, call "
            f"{agent_capabilities.get_authoring_context.name} with kind='first_use' before choosing "
            "tools. That context is a compact orientation and intent router: follow it with the one "
            "task-specific context relevant to the request instead of loading every guide. "
            "For multisite image assembly or image-result quality control, use the registered "
            "image_analysis_workflow context as the canonical operating guide rather than "
            "reconstructing its rules from onboarding text. "
            "Return to these operating guides after a handoff or when the task changes; "
            "they are useful beyond first use. Then call "
            f"{agent_capabilities.search_capabilities.name} with task-relevant workflow, target, "
            "or text filters; its registry-owned workflow groups, target contexts, side effects, "
            "and security metadata are the authority for selecting the safe tool for that route. "
            f"Use {agent_capabilities.list_capabilities.name} only when the complete selected "
            "surface is required. Registered context "
            f"kinds are: {authoring_context_kinds}. "
            "Start read-only. Inspect the source model and take bounded representative samples "
            "before authoring or loading image data. Keep ingestion and semantic selection "
            "separate: recognized HCS layouts retain their native handler; CZI, OME-TIFF, and "
            "other supported rich containers retain Bio-Formats/store decoding. "
            "SourceBindingsConfig may name or select the planes emitted after discovery; "
            "SourceBindingsSource is the fallback ingestion owner only for an otherwise "
            "unrecognized arbitrary-file folder. "
            "Choose the state owner from user intent. A UI-visible request uses capabilities for "
            "the already-running OpenHCS GUI; use a headless route only when UI visibility is not "
            "required. Both routes project the same typed declarations. "
            "Use exposed MCP capabilities for UI and viewer interaction; do not inject "
            "keyboard or mouse input through operating-system automation or a viewer console. "
            "When an operation is missing, search the capability registry and record the "
            "missing contract. During authorised engineering work, extend the existing "
            "declaration-owned MCP/viewer control path in its owning package and validate "
            "the running endpoint. Do not add a bypass or mirror metadata or state. "
            "One pipeline is a PipelineDocument containing PipelineConfig and an ordered "
            "list[FunctionStep]. Use "
            f"{agent_capabilities.describe_config_schema.name} to obtain authoritative nested "
            "configuration fields and valid values. Search/read focused knowledge with "
            f"{agent_capabilities.search_knowledge.name} and "
            f"{agent_capabilities.get_knowledge_document.name} before inventing pipeline "
            "structure. Review the target mutation, refresh revision/request tokens, compile "
            "before running, then validate structured execution results and bounded viewer "
            "evidence. Local file access remains restricted by AgentPathPolicy."
        )


class HostedHttpCapabilityTransportSemantics(CapabilityTransportSemanticsABC):
    """Instructions for the audited read-only hosted capability surface."""

    def server_instructions(self) -> str:
        return (
            "OpenHCS hosted tools expose only the capability declarations audited for "
            "server-side use. Call "
            f"{agent_capabilities.search_capabilities.name} with task-relevant filters before "
            f"choosing a tool; use {agent_capabilities.list_capabilities.name} only for the "
            "complete selected surface. This "
            "surface provides read-only packaged knowledge, architecture, processing-function, "
            "and configuration-schema discovery. It cannot access client-local files, GUI "
            "bridges, viewer windows, runtime processes, draft state, or execution sessions."
        )


class CapabilityTransport(Enum):
    """MCP exposure boundary carrying its nominal server semantics."""

    _semantics_type: type[CapabilityTransportSemanticsABC]

    LOCAL_STDIO = ("local_stdio", LocalStdioCapabilityTransportSemantics)
    HOSTED_STREAMABLE_HTTP = (
        "hosted_streamable_http",
        HostedHttpCapabilityTransportSemantics,
    )

    def __new__(
        cls,
        wire_value: str,
        semantics_type: type[CapabilityTransportSemanticsABC],
    ) -> Self:
        member = object.__new__(cls)
        member._value_ = wire_value
        member._semantics_type = semantics_type
        return member

    def server_instructions(self) -> str:
        """Render instructions through this member's nominal leaf."""
        return self._semantics_type().server_instructions()


class CapabilityWorkflowGroup(Enum):
    """Agent-facing workflow group for capability exposition."""

    DISCOVERY = "discovery"
    KNOWLEDGE = "knowledge"
    FUNCTION_AUTHORING = "function_authoring"
    PIPELINE_AUTHORING = "pipeline_authoring"
    PLATE_DATA = "plate_data"
    UI_SELECTED_PLATE = "ui_selected_plate"
    HEADLESS_EXECUTION = "headless_execution"
    RUNTIME_DIAGNOSTICS = "runtime_diagnostics"
    UI_CONTROL = "ui_control"
    UI_STATE_EDITING = "ui_state_editing"
    VIEWER_REVIEW = "viewer_review"
    BENCHMARKING = "benchmarking"

    @property
    def title(self) -> str:
        return _enum_member_title(self)


class CapabilityWorkflowStage(Enum):
    """Workflow stage occupied by one agent capability."""

    DISCOVERY = "discovery"
    CONTEXT = "context"
    AUTHORING = "authoring"
    DATA_PREPARATION = "data_preparation"
    VALIDATION = "validation"
    EXECUTION = "execution"
    STATUS = "status"
    INSPECTION = "inspection"
    CONTROL = "control"
    STATE_EDITING = "state_editing"
    DIAGNOSTIC = "diagnostic"


class CapabilityTargetContext(Enum):
    """Runtime or data authority targeted by an agent capability."""

    SERVER = "server"
    KNOWLEDGE_BASE = "knowledge_base"
    ARCHITECTURE_MODEL = "architecture_model"
    FUNCTION_REGISTRY = "function_registry"
    CONFIG_DRAFT = "config_draft"
    PIPELINE_DRAFT = "pipeline_draft"
    PLATE_PATH = "plate_path"
    UI_SELECTED_PLATE = "ui_selected_plate"
    HEADLESS_SESSION = "headless_session"
    SUBMITTED_JOB = "submitted_job"
    RUNTIME_SERVER = "runtime_server"
    UI_BRIDGE = "ui_bridge"
    UI_WINDOW = "ui_window"
    UI_OBJECT_STATE = "ui_object_state"
    UI_CODE_DOCUMENT = "ui_code_document"
    VIEWER_WINDOW = "viewer_window"
    BENCHMARK_RUN = "benchmark_run"


class CapabilityVisibility(Enum):
    """Default audience visibility for grouped capability projections."""

    BEGINNER = "beginner"
    STANDARD = "standard"
    EXPERT = "expert"


class CapabilityRole(Enum):
    """Capability role inside an agent-facing workflow group."""

    PRIMARY = "primary"
    MODE_VARIANT = "mode_variant"
    FALLBACK = "fallback"
    DIAGNOSTIC = "diagnostic"
    EXPERT = "expert"


class LocalCapabilitySurfaceProfile(ABC, metaclass=AutoRegisterMeta):
    """Registered local MCP surface policy over declared exposition metadata."""

    __registry__: ClassVar[dict[str, type["LocalCapabilitySurfaceProfile"]]] = {}
    __registry_key__ = "name"
    __skip_if_no_key__ = True

    name: ClassVar[str | None] = None
    title: ClassVar[str]
    distribution_base_extras: ClassVar[tuple[str, ...]] = ("mcp",)

    @classmethod
    def for_name(cls, name: str) -> "LocalCapabilitySurfaceProfile":
        try:
            return cls.__registry__[name]()
        except KeyError as exc:
            raise ValueError(f"Unknown local MCP surface profile: {name!r}.") from exc

    @classmethod
    def names(cls) -> tuple[str, ...]:
        return tuple(cls.__registry__)

    @classmethod
    def names_including(
        cls,
        capability: type["AgentCapabilityDeclaration"],
    ) -> tuple[str, ...]:
        """Return registered surface names that include one capability."""

        return tuple(
            name
            for name in cls.names()
            if capability.supports_surface_profile(cls.for_name(name))
        )

    def includes(self, capability: type["AgentCapabilityDeclaration"]) -> bool:
        """Return whether this profile includes one nominal capability."""
        del capability
        return True

    def distribution_extras(
        self,
        capabilities: tuple[type["AgentCapabilityDeclaration"], ...],
    ) -> tuple[str, ...]:
        """Return package extras required by this selected local surface."""
        extras = dict.fromkeys(self.distribution_base_extras)
        for capability in capabilities:
            if self.includes(capability):
                extras.update(dict.fromkeys(capability.required_extras))
        return tuple(extras)


class NonExpertCapabilitySurfaceMixin:
    """Exclude declarations intentionally marked expert-only or fallback."""

    def includes(self, capability: type["AgentCapabilityDeclaration"]) -> bool:
        return (
            capability.exposition.visibility is not CapabilityVisibility.EXPERT
            and capability.exposition.role not in (CapabilityRole.EXPERT, CapabilityRole.FALLBACK)
            and super().includes(capability)
        )


class WorkflowGroupCapabilitySurfaceMixin:
    """Restrict a surface to authoritative workflow-group declarations."""

    workflow_groups: ClassVar[frozenset[CapabilityWorkflowGroup]]

    def includes(self, capability: type["AgentCapabilityDeclaration"]) -> bool:
        return capability.exposition.workflow_group in self.workflow_groups and super().includes(
            capability
        )


class SelfContainedCapabilitySurfaceMixin:
    """Exclude capabilities requiring a separately running external runtime."""

    def includes(self, capability: type["AgentCapabilityDeclaration"]) -> bool:
        return not capability.runtime_requirements and super().includes(capability)


class FullLocalCapabilitySurfaceProfile(LocalCapabilitySurfaceProfile):
    name: ClassVar[str] = "full"
    title = "Full local development surface"


class DesktopLocalCapabilitySurfaceProfile(
    WorkflowGroupCapabilitySurfaceMixin,
    NonExpertCapabilitySurfaceMixin,
    LocalCapabilitySurfaceProfile,
):
    name: ClassVar[str] = "desktop"
    title = "Desktop user surface"
    distribution_base_extras = ("gui", "mcp")
    workflow_groups = frozenset(
        (
            CapabilityWorkflowGroup.DISCOVERY,
            CapabilityWorkflowGroup.KNOWLEDGE,
            CapabilityWorkflowGroup.FUNCTION_AUTHORING,
            CapabilityWorkflowGroup.PIPELINE_AUTHORING,
            CapabilityWorkflowGroup.PLATE_DATA,
            CapabilityWorkflowGroup.UI_SELECTED_PLATE,
            CapabilityWorkflowGroup.HEADLESS_EXECUTION,
            CapabilityWorkflowGroup.UI_CONTROL,
            CapabilityWorkflowGroup.UI_STATE_EDITING,
            CapabilityWorkflowGroup.VIEWER_REVIEW,
        )
    )


class AuthoringLocalCapabilitySurfaceProfile(
    WorkflowGroupCapabilitySurfaceMixin,
    NonExpertCapabilitySurfaceMixin,
    LocalCapabilitySurfaceProfile,
):
    name: ClassVar[str] = "authoring"
    title = "Authoring surface"
    workflow_groups = frozenset(
        (
            CapabilityWorkflowGroup.DISCOVERY,
            CapabilityWorkflowGroup.KNOWLEDGE,
            CapabilityWorkflowGroup.FUNCTION_AUTHORING,
            CapabilityWorkflowGroup.PIPELINE_AUTHORING,
        )
    )


class CoreLocalCapabilitySurfaceProfile(
    SelfContainedCapabilitySurfaceMixin,
    WorkflowGroupCapabilitySurfaceMixin,
    NonExpertCapabilitySurfaceMixin,
    LocalCapabilitySurfaceProfile,
):
    name: ClassVar[str] = "core"
    title = "Core local workflow surface"
    workflow_groups = frozenset(
        (
            *AuthoringLocalCapabilitySurfaceProfile.workflow_groups,
            CapabilityWorkflowGroup.PLATE_DATA,
            CapabilityWorkflowGroup.HEADLESS_EXECUTION,
        )
    )


@dataclass(frozen=True, slots=True)
class AgentCapabilityExposition:
    """Complete nominal exposition contract for one agent capability."""

    workflow_group: CapabilityWorkflowGroup
    workflow_stage: CapabilityWorkflowStage
    target_context: CapabilityTargetContext
    visibility: CapabilityVisibility
    role: CapabilityRole = CapabilityRole.PRIMARY

    def as_jsonable(self) -> Mapping[str, str]:
        """Project every declared exposition facet through its enum owner."""

        return {
            declared_field.name: getattr(self, declared_field.name).value
            for declared_field in dataclass_fields(self)
        }

    def refine(
        self,
        *,
        workflow_group: CapabilityWorkflowGroup | None = None,
        workflow_stage: CapabilityWorkflowStage | None = None,
        target_context: CapabilityTargetContext | None = None,
        visibility: CapabilityVisibility | None = None,
        role: CapabilityRole | None = None,
    ) -> "AgentCapabilityExposition":
        """Return a typed refinement owned by an inherited capability family."""
        return AgentCapabilityExposition(
            workflow_group=(
                self.workflow_group if workflow_group is None else workflow_group
            ),
            workflow_stage=(
                self.workflow_stage if workflow_stage is None else workflow_stage
            ),
            target_context=(
                self.target_context if target_context is None else target_context
            ),
            visibility=self.visibility if visibility is None else visibility,
            role=self.role if role is None else role,
        )


@dataclass(frozen=True, slots=True)
class AgentScalarInputContract:
    """Nominal contract for a scalar transport field without a request DTO."""

    field_name: str
    default_value: str | None = None

    @property
    def schema_name(self) -> str:
        return self.field_name


@dataclass(frozen=True, slots=True)
class AgentResultFamilyContract:
    """Actual producer alternatives and their existing external nominal identity.

    MCP's advertised owner is an external metadata fact, not the entire result
    family. Keep those questions distinct while deriving decode membership from
    the producer's declared union. No presentation roster owns that membership.
    """

    advertised_contract: type
    producer: Callable[..., object]

    @property
    def result_type(self) -> UnionType:
        return get_type_hints(self.producer, include_extras=True)["return"]

    @property
    def result_types(self) -> tuple[type, ...]:
        return get_args(self.result_type)

    @property
    def schema_name(self) -> str:
        return self.advertised_contract.__name__


AgentContract: TypeAlias = type | AgentScalarInputContract | AgentResultFamilyContract


def _enum_member_title(value: Enum) -> str:
    return " ".join(
        token if token.isupper() and len(token) <= 3 else token.lower().title()
        for token in value.name.split("_")
    )


def _contract_schema_name(contract: AgentContract | None) -> str | None:
    if contract is None:
        return None
    if isinstance(contract, (AgentScalarInputContract, AgentResultFamilyContract)):
        return contract.schema_name
    return contract.__name__


def require_agent_type_contract(contract: AgentContract | None) -> type:
    if isinstance(contract, AgentResultFamilyContract):
        return contract.advertised_contract
    if not isinstance(contract, type):
        raise TypeError(f"Expected agent type contract, got {contract!r}.")
    return contract


def _keyword_parameter(name: str, annotation: object, default: object) -> Parameter:
    return Parameter(name, Parameter.KEYWORD_ONLY, default=default, annotation=annotation)


class AgentCapabilityInvocation(ABC):
    """Execution shape of one capability.

    The shape owns everything a transport needs to expose the capability: its
    ``execute``, the MCP parameters and their decoding into call arguments, its
    MCP registration, and its CLI projection. Leaves compose an input mixin and
    optionally a connection mixin over an execute owner; parameters and call
    arguments accumulate along the MRO, so the composition order is the public
    parameter order. Transport primitives arrive as ports: the MCP binder owned
    by ``openhcs.mcp.server`` and the CLI projection owned by the dev client.
    """

    __slots__ = ()

    kind: ClassVar[CapabilityKind] = CapabilityKind.TOOL
    allow_stale_server: ClassVar[bool] = False

    @abstractmethod
    def execute(self, context: object, *arguments: object) -> object:
        """Run the capability against its execution context."""

    def tool_parameters(
        self,
        declaration: type[AgentCapabilityDeclaration],
        binder: McpCapabilityBinder,
    ) -> tuple[Parameter, ...]:
        return ()

    def call_arguments(
        self,
        declaration: type[AgentCapabilityDeclaration],
        binder: McpCapabilityBinder,
        arguments: Mapping[str, object],
    ) -> tuple[object, ...]:
        return ()

    def invoke(
        self,
        declaration: type[AgentCapabilityDeclaration],
        binder: McpCapabilityBinder,
        arguments: Mapping[str, object],
    ) -> object:
        return self.execute(
            binder.context,
            *self.call_arguments(declaration, binder, arguments),
        )

    def bind_mcp(
        self,
        declaration: type[AgentCapabilityDeclaration],
        binder: McpCapabilityBinder,
    ) -> None:
        binder.register_tool(declaration, self)

    def configure_cli(
        self,
        declaration: type[AgentCapabilityDeclaration],
        parser: ArgumentParser,
        cli: McpDevCliProjection,
    ) -> None:
        """Add the CLI arguments this shape's inputs require."""

    def cli_tool_arguments(
        self,
        declaration: type[AgentCapabilityDeclaration],
        args: Namespace,
        cli: McpDevCliProjection,
    ) -> dict[str, object]:
        return {}

    def cli_timeout_seconds(
        self,
        args: Namespace,
        timeout_seconds: float,
        cli: McpDevCliProjection,
    ) -> float:
        return timeout_seconds


@dataclass(frozen=True, slots=True)
class AgentFunctionInvocation(AgentCapabilityInvocation):
    """Execute a context-free function."""

    function: Callable[..., object]

    def execute(self, context: object, *arguments: object) -> object:
        del context
        return self.function(*arguments)


@dataclass(frozen=True, slots=True)
class AgentServiceInvocation(AgentCapabilityInvocation):
    """Execute one method of a service resolved from the agent context."""

    service: Callable[[object], object]
    method: Callable[..., object]

    def execute(self, context: object, *arguments: object) -> object:
        return self.method(self.service(context), *arguments)


class AgentServerHealthInvocation(AgentCapabilityInvocation):
    """Process health owned by the serving transport; answers while stale."""

    __slots__ = ()

    allow_stale_server = True

    def execute(self, context: McpCapabilityBinder, *arguments: object) -> object:
        del arguments
        return context.server_health()

    def invoke(
        self,
        declaration: type[AgentCapabilityDeclaration],
        binder: McpCapabilityBinder,
        arguments: Mapping[str, object],
    ) -> object:
        del declaration, arguments
        return self.execute(binder)


class AgentResourceInvocationMixin:
    """A no-argument read registered as an MCP resource instead of a tool."""

    __slots__ = ()

    kind: ClassVar[CapabilityKind] = CapabilityKind.RESOURCE


    def bind_mcp(
        self,
        declaration: type[AgentCapabilityDeclaration],
        binder: McpCapabilityBinder,
    ) -> None:
        binder.register_resource(declaration, self)


class AgentResourceFunctionInvocation(
    AgentResourceInvocationMixin,
    AgentFunctionInvocation,
):
    __slots__ = ()


class AgentResourceServiceInvocation(
    AgentResourceInvocationMixin,
    AgentServiceInvocation,
):
    __slots__ = ()


class AgentScalarInputMixin:
    """One string declared by the capability's ``AgentScalarInputContract``."""

    __slots__ = ()

    @staticmethod
    def scalar_contract(
        declaration: type[AgentCapabilityDeclaration],
    ) -> AgentScalarInputContract:
        contract = declaration.input_contract
        if not isinstance(contract, AgentScalarInputContract):
            raise TypeError(
                f"{declaration.__name__} requires AgentScalarInputContract, "
                f"got {contract!r}."
            )
        return contract

    def tool_parameters(self, declaration, binder):
        contract = self.scalar_contract(declaration)
        return (
            _keyword_parameter(
                contract.field_name,
                str,
                (
                    Parameter.empty
                    if contract.default_value is None
                    else contract.default_value
                ),
            ),
            *super().tool_parameters(declaration, binder),
        )

    def call_arguments(self, declaration, binder, arguments):
        return (
            arguments[self.scalar_contract(declaration).field_name],
            *super().call_arguments(declaration, binder, arguments),
        )

    def configure_cli(self, declaration, parser, cli):
        contract = self.scalar_contract(declaration)
        if contract.default_value is None:
            parser.add_argument(contract.field_name)
        else:
            parser.add_argument(
                contract.field_name,
                nargs="?",
                default=contract.default_value,
            )
        super().configure_cli(declaration, parser, cli)

    def cli_tool_arguments(self, declaration, args, cli):
        field_name = self.scalar_contract(declaration).field_name
        return {
            field_name: vars(args)[field_name],
            **super().cli_tool_arguments(declaration, args, cli),
        }


class AgentRequestInputMixin:
    """A typed request DTO declared as the capability's input contract."""

    __slots__ = ()

    @staticmethod
    def request_type(declaration: type[AgentCapabilityDeclaration]) -> type:
        return require_agent_type_contract(declaration.input_contract)

    def configure_cli(self, declaration, parser, cli):
        cli.configure_request(parser, self.request_type(declaration))
        super().configure_cli(declaration, parser, cli)

    def cli_tool_arguments(self, declaration, args, cli):
        return {
            **cli.request_tool_arguments(args, self.request_type(declaration)),
            **super().cli_tool_arguments(declaration, args, cli),
        }


class AgentFromFieldsInputMixin(AgentRequestInputMixin):
    """Request DTO whose public parameters are its ``from_fields`` factory."""

    __slots__ = ()

    def tool_parameters(self, declaration, binder):
        request_type = self.request_type(declaration)
        factory = request_type.from_fields
        type_hints = get_type_hints(factory)
        return (
            *(
                _keyword_parameter(
                    parameter.name,
                    binder.request_annotation(
                        request_type, parameter.name, type_hints[parameter.name]
                    ),
                    parameter.default,
                )
                for parameter in inspect_signature(factory).parameters.values()
            ),
            *super().tool_parameters(declaration, binder),
        )

    def call_arguments(self, declaration, binder, arguments):
        factory = self.request_type(declaration).from_fields
        return (
            factory(
                **{
                    parameter_name: arguments[parameter_name]
                    for parameter_name in inspect_signature(factory).parameters
                }
            ),
            *super().call_arguments(declaration, binder, arguments),
        )


class AgentDataclassInputMixin(AgentRequestInputMixin):
    """Dataclass request DTO whose fields are the public parameters."""

    __slots__ = ()

    def tool_parameters(self, declaration, binder):
        request_type = self.request_type(declaration)
        type_hints = get_type_hints(request_type)
        parameters = []
        for request_field in dataclass_fields(request_type):
            if request_field.default_factory is not MISSING:
                raise TypeError(
                    f"{declaration.__name__} cannot expose default_factory field "
                    f"{request_field.name!r} as a direct MCP parameter."
                )
            parameters.append(
                _keyword_parameter(
                    request_field.name,
                    binder.request_annotation(
                        request_type,
                        request_field.name,
                        type_hints[request_field.name],
                    ),
                    (
                        Parameter.empty
                        if request_field.default is MISSING
                        else request_field.default
                    ),
                )
            )
        return (*parameters, *super().tool_parameters(declaration, binder))

    def call_arguments(self, declaration, binder, arguments):
        request_type = self.request_type(declaration)
        return (
            request_type(
                **{
                    request_field.name: arguments[request_field.name]
                    for request_field in dataclass_fields(request_type)
                }
            ),
            *super().call_arguments(declaration, binder, arguments),
        )


class AgentConfigPatchInputMixin:
    """``ConfigPatch`` input with its values supplied as one JSON object."""

    __slots__ = ()

    def tool_parameters(self, declaration, binder):
        config_type_field, values_field = dataclass_fields(ConfigPatch)
        return (
            _keyword_parameter(config_type_field.name, str, Parameter.empty),
            _keyword_parameter(values_field.name, dict | None, None),
            *super().tool_parameters(declaration, binder),
        )

    def call_arguments(self, declaration, binder, arguments):
        config_type_field, values_field = dataclass_fields(ConfigPatch)
        values = arguments[values_field.name]
        return (
            ConfigPatch(
                config_type=arguments[config_type_field.name],
                values={} if values is None else dict(values),
            ),
            *super().call_arguments(declaration, binder, arguments),
        )


class AgentUiConnectionMixin:
    """Running-UI bridge connection resolved from the MCP connection request."""

    __slots__ = ()

    def tool_parameters(self, declaration, binder):
        return (
            *super().tool_parameters(declaration, binder),
            binder.ui_connection_parameter(),
        )

    def call_arguments(self, declaration, binder, arguments):
        return (
            *super().call_arguments(declaration, binder, arguments),
            binder.ui_connection(arguments),
        )

    def configure_cli(self, declaration, parser, cli):
        cli.configure_ui_connection(parser)
        super().configure_cli(declaration, parser, cli)

    def cli_tool_arguments(self, declaration, args, cli):
        return {
            **super().cli_tool_arguments(declaration, args, cli),
            **cli.ui_connection_arguments(args),
        }

    def cli_timeout_seconds(self, args, timeout_seconds, cli):
        return cli.ui_timeout_seconds(args, timeout_seconds)


class AgentCompactActionsProjectionMixin:
    """MCP-side action compaction owned by the widget-tree result DTO."""

    __slots__ = ()

    def tool_parameters(self, declaration, binder):
        return (
            *super().tool_parameters(declaration, binder),
            _keyword_parameter("compact_actions", bool, True),
        )

    def invoke(self, declaration, binder, arguments):
        return super().invoke(declaration, binder, arguments).as_jsonable(
            compact_actions=bool(arguments["compact_actions"]),
        )


class AgentViewerWindowConnectionMixin:
    """Viewer endpoint connection fields building the declared request."""

    __slots__ = ()

    @staticmethod
    def request_type(
        declaration: type[AgentCapabilityDeclaration],
    ) -> type[ViewerWindowControlRequest]:
        contract = require_agent_type_contract(declaration.input_contract)
        if not issubclass(contract, ViewerWindowControlRequest):
            raise TypeError(
                f"{declaration.__name__} requires a ViewerWindowControlRequest "
                f"input contract, got {contract!r}."
            )
        return contract

    def option_parameters(
        self,
        request_type: type[ViewerWindowControlRequest],
    ) -> tuple[Parameter, ...]:
        return ()

    def viewer_request(self, request_type, control, arguments):
        del arguments
        return request_type(
            connection=control.connection,
            timeout_ms=control.timeout_ms,
        )

    def tool_parameters(self, declaration, binder):
        return (
            *binder.viewer_connection_parameters(),
            *self.option_parameters(self.request_type(declaration)),
            *super().tool_parameters(declaration, binder),
        )

    def call_arguments(self, declaration, binder, arguments):
        return (
            self.viewer_request(
                self.request_type(declaration),
                binder.viewer_control(arguments),
                arguments,
            ),
            *super().call_arguments(declaration, binder, arguments),
        )

    def configure_cli(self, declaration, parser, cli):
        cli.configure_viewer_connection(parser)
        super().configure_cli(declaration, parser, cli)

    def cli_tool_arguments(self, declaration, args, cli):
        return {
            **cli.viewer_connection_arguments(args),
            **super().cli_tool_arguments(declaration, args, cli),
        }


class AgentViewerWindowOptionsMixin(AgentViewerWindowConnectionMixin):
    """Viewer connection plus the request factory's own option fields."""

    __slots__ = ()

    def option_parameters(self, request_type):
        factory = request_type.from_fields
        type_hints = get_type_hints(factory, include_extras=True)
        injected_names = ViewerWindowControlRequest.factory_injected_field_names()
        return tuple(
            _keyword_parameter(
                parameter.name, type_hints[parameter.name], parameter.default
            )
            for parameter in inspect_signature(factory).parameters.values()
            if parameter.name not in injected_names
        )

    def viewer_request(self, request_type, control, arguments):
        return request_type.from_fields(
            connection=control.connection,
            timeout_ms=control.timeout_ms,
            **{
                parameter.name: arguments[parameter.name]
                for parameter in self.option_parameters(request_type)
            },
        )


class AgentScalarServiceInvocation(AgentScalarInputMixin, AgentServiceInvocation):
    __slots__ = ()


class AgentFromFieldsServiceInvocation(
    AgentFromFieldsInputMixin,
    AgentServiceInvocation,
):
    __slots__ = ()


class AgentDataclassRequestServiceInvocation(
    AgentDataclassInputMixin,
    AgentServiceInvocation,
):
    __slots__ = ()


class AgentConfigPatchServiceInvocation(
    AgentConfigPatchInputMixin,
    AgentServiceInvocation,
):
    __slots__ = ()


class AgentConnectionServiceInvocation(AgentUiConnectionMixin, AgentServiceInvocation):
    __slots__ = ()


class AgentConnectionScalarServiceInvocation(
    AgentUiConnectionMixin,
    AgentScalarInputMixin,
    AgentServiceInvocation,
):
    __slots__ = ()


class AgentConnectionRequestServiceInvocation(
    AgentUiConnectionMixin,
    AgentFromFieldsInputMixin,
    AgentServiceInvocation,
):
    __slots__ = ()


class AgentUiWidgetTreeServiceInvocation(
    AgentUiConnectionMixin,
    AgentCompactActionsProjectionMixin,
    AgentFromFieldsInputMixin,
    AgentServiceInvocation,
):
    __slots__ = ()


class AgentViewerWindowConnectionServiceInvocation(
    AgentViewerWindowConnectionMixin,
    AgentServiceInvocation,
):
    __slots__ = ()


class AgentViewerWindowRequestServiceInvocation(
    AgentViewerWindowOptionsMixin,
    AgentServiceInvocation,
):
    __slots__ = ()


@dataclass(frozen=True, slots=True)
class AgentCapabilityRegistryRequestInvocation(
    AgentDataclassInputMixin,
    AgentCapabilityInvocation,
):
    """Typed query whose execution context is the surface-selected registry."""

    method: Callable[..., object]

    def execute(self, context: object, *arguments: object) -> object:
        return self.method(context, *arguments)

    def invoke(self, declaration, binder, arguments):
        return self.execute(
            binder.selected_registry,
            *self.call_arguments(declaration, binder, arguments),
        )

@dataclass(frozen=True, slots=True)
class AgentCapabilitySearchRequest:
    """Bounded registry query over declaration-owned capability metadata."""

    DEFAULT_LIMIT: ClassVar[int] = 12
    MAXIMUM_LIMIT: ClassVar[int] = 50

    text: str | None = field(
        default=None,
        metadata={
            AGENT_PARAMETER_DESCRIPTION_METADATA_KEY: (
                "Whitespace-separated terms matched across declared capability name, "
                "title, description, service, workflow metadata, side effects, "
                "requirements, and data exposure."
            )
        },
    )
    kind: CapabilityKind | None = None
    workflow_group: CapabilityWorkflowGroup | None = None
    workflow_stage: CapabilityWorkflowStage | None = None
    target_context: CapabilityTargetContext | None = None
    visibility: CapabilityVisibility | None = None
    role: CapabilityRole | None = None
    has_side_effects: bool | None = field(
        default=None,
        metadata={
            AGENT_PARAMETER_DESCRIPTION_METADATA_KEY: (
                "True selects declarations with side effects; false selects "
                "declarations whose side-effect tuple is empty."
            )
        },
    )
    side_effect_contains: str | None = field(
        default=None,
        metadata={
            AGENT_PARAMETER_DESCRIPTION_METADATA_KEY: (
                "Case-insensitive substring matched against each declaration-owned "
                "side-effect value."
            )
        },
    )
    offset: int = field(
        default=0,
        metadata={
            AGENT_PARAMETER_DESCRIPTION_METADATA_KEY: (
                "Zero-based offset applied after every task filter."
            )
        },
    )
    limit: int = field(
        default=DEFAULT_LIMIT,
        metadata={
            AGENT_PARAMETER_DESCRIPTION_METADATA_KEY: (
                f"Maximum summaries returned in one page (1..{MAXIMUM_LIMIT})."
            )
        },
    )

    def __post_init__(self) -> None:
        if self.offset < 0:
            raise ValueError("Capability search offset must be non-negative.")
        if not 1 <= self.limit <= self.MAXIMUM_LIMIT:
            raise ValueError(
                f"Capability search limit must be between 1 and {self.MAXIMUM_LIMIT}."
            )

    def matches(self, capability: type[AgentCapabilityDeclaration]) -> bool:
        """Return whether one canonical capability matches every query facet."""

        exposition = capability.exposition
        exact_facets = (
            (self.kind, capability.kind),
            (self.workflow_group, exposition.workflow_group),
            (self.workflow_stage, exposition.workflow_stage),
            (self.target_context, exposition.target_context),
            (self.visibility, exposition.visibility),
            (self.role, exposition.role),
        )
        if any(
            requested is not None and requested is not actual
            for requested, actual in exact_facets
        ):
            return False
        if (
            self.has_side_effects is not None
            and bool(capability.side_effects) is not self.has_side_effects
        ):
            return False
        side_effect_needle = (
            None
            if self.side_effect_contains is None
            else self.side_effect_contains.strip().casefold()
        )
        if side_effect_needle and not any(
            side_effect_needle in side_effect.casefold()
            for side_effect in capability.side_effects
        ):
            return False
        search_terms = (
            () if self.text is None else tuple(self.text.strip().casefold().split())
        )
        if not search_terms:
            return True
        searchable_text = "\n".join(
            value.casefold() for value in self._searchable_metadata(capability) if value
        )
        return all(term in searchable_text for term in search_terms)

    @staticmethod
    def _searchable_metadata(
        capability: type[AgentCapabilityDeclaration],
    ) -> tuple[str, ...]:
        """Project text search input directly from one canonical capability."""

        return (
            capability.name,
            capability.title,
            capability.description,
            capability.service,
            capability.kind.value,
            *capability.exposition.as_jsonable().values(),
            *capability.side_effects,
            *capability.required_extras,
            *capability.runtime_requirements,
            *capability.data_exposure,
            *capability.security_requirements,
        )


@dataclass(frozen=True, slots=True)
class AgentCapabilitySummary:
    """Compact task-routing projection constructed by the declaration."""

    name: str
    kind: CapabilityKind
    title: str
    description: str
    workflow_group: CapabilityWorkflowGroup
    workflow_stage: CapabilityWorkflowStage
    target_context: CapabilityTargetContext
    visibility: CapabilityVisibility
    role: CapabilityRole
    read_only: bool
    side_effects: tuple[str, ...]
    requires_network: bool
    required_extras: tuple[str, ...]
    runtime_requirements: tuple[str, ...]
    data_exposure: tuple[str, ...]
    security_requirements: tuple[str, ...]
    input_type: str | None
    output_type: str | None


@dataclass(frozen=True, slots=True)
class AgentCapabilitySearchResult:
    """Bounded task-specific view over one selected capability registry."""

    schema_version: str
    surface_profile: str
    query: AgentCapabilitySearchRequest
    matched_count: int
    returned_count: int
    next_offset: int | None
    capabilities: tuple[AgentCapabilitySummary, ...]


@dataclass(frozen=True, slots=True)
class AgentCapabilitySurfaceSelection:
    """Transport and local-profile policy used by every capability consumer."""

    transport: CapabilityTransport | None = None
    local_profile: LocalCapabilitySurfaceProfile = field(
        default_factory=FullLocalCapabilitySurfaceProfile
    )

    def includes(self, capability: type[AgentCapabilityDeclaration]) -> bool:
        return (
            self.transport is None or capability.supports_transport(self.transport)
        ) and capability.supports_surface_profile(self.local_profile)


class AgentCapabilityDeclarationMeta(AutoRegisterMeta):
    """Facets every capability derives from its own declared attributes."""

    def __init__(cls, name, bases, namespace, **kwargs) -> None:
        super().__init__(name, bases, namespace, **kwargs)
        if cls.name is None:
            return
        try:
            invocation = cls.invocation
            exposition = cls.exposition
        except AttributeError as exc:
            raise TypeError(
                f"{cls.__name__} must declare its invocation and exposition."
            ) from exc
        if not isinstance(invocation, AgentCapabilityInvocation):
            raise TypeError(
                f"{cls.__name__}.invocation must be an AgentCapabilityInvocation."
            )
        if not isinstance(exposition, AgentCapabilityExposition):
            raise TypeError(
                f"{cls.__name__}.exposition must be an AgentCapabilityExposition."
            )
        if not cls.transport_availability or len(cls.transport_availability) != len(
            set(cls.transport_availability)
        ):
            raise ValueError(
                f"Capability {cls.name!r} must declare distinct transports."
            )
        if cls.mutating is not bool(cls.side_effects):
            raise ValueError(
                f"Capability {cls.name!r} must declare side_effects exactly when "
                "it is mutating."
            )
        if cls.progress_heartbeat_seconds is not None and (
            not isfinite(cls.progress_heartbeat_seconds)
            or cls.progress_heartbeat_seconds <= 0
        ):
            raise ValueError("progress_heartbeat_seconds must be positive and finite.")

    @property
    def kind(cls) -> CapabilityKind:
        """The wire kind of the capability's invocation shape."""
        return cls.invocation.kind

    @property
    def read_only(cls) -> bool:
        """Return the declaration-owned mutation classification."""
        return not cls.mutating and not cls.side_effects

    @property
    def input_type(cls) -> str | None:
        return _contract_schema_name(cls.input_contract)

    @property
    def output_type(cls) -> str | None:
        return _contract_schema_name(cls.output_contract)

    @property
    def output_contract_types(cls) -> tuple[type, ...]:
        if isinstance(cls.output_contract, AgentResultFamilyContract):
            return cls.output_contract.result_types
        return (
            ()
            if cls.output_contract is None
            else (require_agent_type_contract(cls.output_contract),)
        )


class AgentCapabilityDeclaration(ABC, metaclass=AgentCapabilityDeclarationMeta):
    """Registered declaration for one agent-facing capability.

    The declaration class is the capability: transports, the registry and the
    CLI read it directly. Its execution shape is the declared ``invocation``.
    """

    __registry__: ClassVar[dict[str, type["AgentCapabilityDeclaration"]]] = {}
    __registry_key__ = "name"
    __skip_if_no_key__ = True

    name: ClassVar[str | None] = None
    title: ClassVar[str]
    description: ClassVar[str]
    service: ClassVar[str]
    cli_command: ClassVar[str | None] = None
    cli_aliases: ClassVar[tuple[str, ...]] = ()
    transport_availability: ClassVar[tuple[CapabilityTransport, ...]] = (
        CapabilityTransport.LOCAL_STDIO,
    )
    mutating: ClassVar[bool] = False
    side_effects: ClassVar[tuple[str, ...]] = ()
    requires_network: ClassVar[bool] = False
    required_extras: ClassVar[tuple[str, ...]] = ()
    runtime_requirements: ClassVar[tuple[str, ...]] = ()
    data_exposure: ClassVar[tuple[str, ...]] = ()
    security_requirements: ClassVar[tuple[str, ...]] = ()
    progress_heartbeat_seconds: ClassVar[float | None] = None
    progress_worker_thread_safe: ClassVar[bool] = True
    input_contract: ClassVar[AgentContract | None] = None
    output_contract: ClassVar[AgentContract | None] = None
    exposition: ClassVar[AgentCapabilityExposition]
    invocation: ClassVar[AgentCapabilityInvocation]

    @classmethod
    def supports_transport(cls, transport: CapabilityTransport) -> bool:
        """Return whether this declaration permits registration on ``transport``."""
        return transport in cls.transport_availability

    @classmethod
    def supports_surface_profile(cls, profile: LocalCapabilitySurfaceProfile) -> bool:
        """Return whether the profile permits this declared visibility tier."""
        return profile.includes(cls)

    @classmethod
    def as_jsonable(cls) -> dict[str, object]:
        return {
            "name": cls.name,
            "kind": cls.kind.value,
            "title": cls.title,
            "description": cls.description,
            "service": cls.service,
            "cli_command": cls.cli_command,
            "cli_aliases": list(cls.cli_aliases),
            "transport_availability": [
                transport.value for transport in cls.transport_availability
            ],
            "mutating": cls.mutating,
            "side_effects": list(cls.side_effects),
            "requires_network": cls.requires_network,
            "required_extras": list(cls.required_extras),
            "runtime_requirements": list(cls.runtime_requirements),
            "data_exposure": list(cls.data_exposure),
            "security_requirements": list(cls.security_requirements),
            "progress_heartbeat_seconds": cls.progress_heartbeat_seconds,
            "progress_worker_thread_safe": cls.progress_worker_thread_safe,
            "input_type": cls.input_type,
            "output_type": cls.output_type,
            **cls.exposition.as_jsonable(),
        }

    @classmethod
    def compact_summary(cls) -> AgentCapabilitySummary:
        """Project task-routing metadata at the canonical capability owner."""

        exposition = cls.exposition
        return AgentCapabilitySummary(
            name=cls.name,
            kind=cls.kind,
            title=cls.title,
            description=cls.description,
            workflow_group=exposition.workflow_group,
            workflow_stage=exposition.workflow_stage,
            target_context=exposition.target_context,
            visibility=exposition.visibility,
            role=exposition.role,
            read_only=cls.read_only,
            side_effects=cls.side_effects,
            requires_network=cls.requires_network,
            required_extras=cls.required_extras,
            runtime_requirements=cls.runtime_requirements,
            data_exposure=cls.data_exposure,
            security_requirements=cls.security_requirements,
            input_type=cls.input_type,
            output_type=cls.output_type,
        )


class HostedTransportCapabilityMixin:
    """Nominal opt-in for capabilities audited as safe on a hosted server."""

    transport_availability: ClassVar[tuple[CapabilityTransport, ...]] = (
        CapabilityTransport.LOCAL_STDIO,
        CapabilityTransport.HOSTED_STREAMABLE_HTTP,
    )


class DiscoveryCapability(AgentCapabilityDeclaration):
    """Capability exposed in the initial server/capability discovery lane."""

    exposition = AgentCapabilityExposition(
        workflow_group=CapabilityWorkflowGroup.DISCOVERY,
        workflow_stage=CapabilityWorkflowStage.DISCOVERY,
        target_context=CapabilityTargetContext.SERVER,
        visibility=CapabilityVisibility.BEGINNER,
    )


class KnowledgeCapability(AgentCapabilityDeclaration):
    """Capability that exposes bounded documentation or authoring context."""

    exposition = AgentCapabilityExposition(
        workflow_group=CapabilityWorkflowGroup.KNOWLEDGE,
        workflow_stage=CapabilityWorkflowStage.CONTEXT,
        target_context=CapabilityTargetContext.KNOWLEDGE_BASE,
        visibility=CapabilityVisibility.BEGINNER,
    )


class ArchitectureCapability(
    HostedTransportCapabilityMixin,
    KnowledgeCapability,
):
    """Capability that exposes source-backed OpenHCS architecture facts."""

    exposition = KnowledgeCapability.exposition.refine(
        target_context=CapabilityTargetContext.ARCHITECTURE_MODEL,
    )


class ProgressAcknowledgedCapability(AgentCapabilityDeclaration):
    """Operations acknowledge activity before the client idle limit."""

    progress_heartbeat_seconds = 1.0


class MainThreadProgressCapability(ProgressAcknowledgedCapability):
    """Compose progress with Qt/ObjectState's original main-thread affinity."""

    progress_worker_thread_safe = False


class FunctionCatalogCapability(ProgressAcknowledgedCapability):
    """Capability that reads or extends the processing-function catalog."""

    exposition = AgentCapabilityExposition(
        workflow_group=CapabilityWorkflowGroup.FUNCTION_AUTHORING,
        workflow_stage=CapabilityWorkflowStage.AUTHORING,
        target_context=CapabilityTargetContext.FUNCTION_REGISTRY,
        visibility=CapabilityVisibility.BEGINNER,
    )


class ConfigDraftCapability(AgentCapabilityDeclaration):
    """Capability that works with typed configuration draft state."""

    exposition = AgentCapabilityExposition(
        workflow_group=CapabilityWorkflowGroup.PIPELINE_AUTHORING,
        workflow_stage=CapabilityWorkflowStage.AUTHORING,
        target_context=CapabilityTargetContext.CONFIG_DRAFT,
        visibility=CapabilityVisibility.STANDARD,
    )


class PipelineDraftCapability(AgentCapabilityDeclaration):
    """Capability that works with pipeline draft or source planning state."""

    exposition = AgentCapabilityExposition(
        workflow_group=CapabilityWorkflowGroup.PIPELINE_AUTHORING,
        workflow_stage=CapabilityWorkflowStage.AUTHORING,
        target_context=CapabilityTargetContext.PIPELINE_DRAFT,
        visibility=CapabilityVisibility.STANDARD,
    )


class PlatePathCapability(AgentCapabilityDeclaration):
    """Capability that works from an explicit local plate path."""

    exposition = AgentCapabilityExposition(
        workflow_group=CapabilityWorkflowGroup.PLATE_DATA,
        workflow_stage=CapabilityWorkflowStage.DATA_PREPARATION,
        target_context=CapabilityTargetContext.PLATE_PATH,
        visibility=CapabilityVisibility.BEGINNER,
    )


class HeadlessExecutionCapability(AgentCapabilityDeclaration):
    """Capability that works with headless execution sessions or jobs."""

    exposition = AgentCapabilityExposition(
        workflow_group=CapabilityWorkflowGroup.HEADLESS_EXECUTION,
        workflow_stage=CapabilityWorkflowStage.EXECUTION,
        target_context=CapabilityTargetContext.HEADLESS_SESSION,
        visibility=CapabilityVisibility.STANDARD,
    )


class SubmittedJobCapability(HeadlessExecutionCapability):
    """Capability that observes a submitted compile or execution job."""

    exposition = HeadlessExecutionCapability.exposition.refine(
        workflow_stage=CapabilityWorkflowStage.STATUS,
        target_context=CapabilityTargetContext.SUBMITTED_JOB,
        role=CapabilityRole.DIAGNOSTIC,
    )


class UiBridgeCapability(AgentCapabilityDeclaration):
    """Capability that targets the running PyQt UI bridge."""

    exposition = AgentCapabilityExposition(
        workflow_group=CapabilityWorkflowGroup.UI_CONTROL,
        workflow_stage=CapabilityWorkflowStage.CONTROL,
        target_context=CapabilityTargetContext.UI_BRIDGE,
        visibility=CapabilityVisibility.STANDARD,
    )


class UiSelectedPlateCapability(UiBridgeCapability):
    """Capability that uses the current PlateManager selection as its plate."""

    exposition = UiBridgeCapability.exposition.refine(
        workflow_group=CapabilityWorkflowGroup.UI_SELECTED_PLATE,
        workflow_stage=CapabilityWorkflowStage.DATA_PREPARATION,
        target_context=CapabilityTargetContext.UI_SELECTED_PLATE,
        role=CapabilityRole.MODE_VARIANT,
    )


class UiWindowCapability(UiBridgeCapability):
    """Capability that targets a visible or focusable PyQt UI window."""

    exposition = UiBridgeCapability.exposition.refine(
        target_context=CapabilityTargetContext.UI_WINDOW,
    )


class UiSemanticActionCapability(UiBridgeCapability):
    """Capability that invokes declared semantic UI actions."""

    exposition = UiBridgeCapability.exposition


class UiWidgetFallbackCapability(UiWindowCapability):
    """Capability that uses generic widget projection as a fallback control."""

    exposition = UiWindowCapability.exposition.refine(
        visibility=CapabilityVisibility.EXPERT,
        role=CapabilityRole.FALLBACK,
    )


class UiCodeDocumentCapability(UiBridgeCapability):
    """Capability that targets UI-owned pycodified code documents."""

    exposition = UiBridgeCapability.exposition.refine(
        workflow_group=CapabilityWorkflowGroup.UI_STATE_EDITING,
        workflow_stage=CapabilityWorkflowStage.STATE_EDITING,
        target_context=CapabilityTargetContext.UI_CODE_DOCUMENT,
    )


class UiObjectStateCapability(UiBridgeCapability):
    """Capability that targets typed ObjectState scopes and fields."""

    exposition = UiBridgeCapability.exposition.refine(
        workflow_group=CapabilityWorkflowGroup.UI_STATE_EDITING,
        workflow_stage=CapabilityWorkflowStage.STATE_EDITING,
        target_context=CapabilityTargetContext.UI_OBJECT_STATE,
        visibility=CapabilityVisibility.EXPERT,
    )


class UiSnapshotCapability(UiObjectStateCapability):
    """Capability that targets ObjectState snapshot or branch time travel."""

    exposition = UiObjectStateCapability.exposition.refine(
        visibility=CapabilityVisibility.STANDARD,
        role=CapabilityRole.PRIMARY,
    )


class ViewerWindowCapability(AgentCapabilityDeclaration):
    """Capability that targets a running viewer window endpoint."""

    exposition = AgentCapabilityExposition(
        workflow_group=CapabilityWorkflowGroup.VIEWER_REVIEW,
        workflow_stage=CapabilityWorkflowStage.INSPECTION,
        target_context=CapabilityTargetContext.VIEWER_WINDOW,
        visibility=CapabilityVisibility.STANDARD,
    )


class RuntimeServerCapability(AgentCapabilityDeclaration):
    """Capability that targets a running OpenHCS runtime server."""

    exposition = AgentCapabilityExposition(
        workflow_group=CapabilityWorkflowGroup.RUNTIME_DIAGNOSTICS,
        workflow_stage=CapabilityWorkflowStage.DIAGNOSTIC,
        target_context=CapabilityTargetContext.RUNTIME_SERVER,
        visibility=CapabilityVisibility.EXPERT,
        role=CapabilityRole.DIAGNOSTIC,
    )


@dataclass(frozen=True, slots=True)
class AgentCapabilityGroup:
    workflow_group: CapabilityWorkflowGroup
    capability_names: tuple[str, ...]
    tool_count: int
    resource_count: int

    @property
    def title(self) -> str:
        return self.workflow_group.title


@dataclass(frozen=True, slots=True)
class AgentCapabilityRegistry:
    schema_version: str
    capabilities: tuple[type[AgentCapabilityDeclaration], ...]
    groups: tuple[AgentCapabilityGroup, ...] = ()
    surface_profile: str = FullLocalCapabilitySurfaceProfile.name

    @property
    def non_read_only_tools(self) -> tuple[type[AgentCapabilityDeclaration], ...]:
        """Return tools whose declarations permit mutation or side effects."""
        return tuple(
            capability
            for capability in self.capabilities
            if capability.kind is CapabilityKind.TOOL and not capability.read_only
        )

    def search(
        self,
        request: AgentCapabilitySearchRequest,
    ) -> AgentCapabilitySearchResult:
        """Filter and page this selected canonical registry."""

        matched = tuple(
            capability
            for capability in self.capabilities
            if request.matches(capability)
        )
        selected = matched[request.offset : request.offset + request.limit]
        returned_end = request.offset + len(selected)
        return AgentCapabilitySearchResult(
            schema_version=self.schema_version,
            surface_profile=self.surface_profile,
            query=request,
            matched_count=len(matched),
            returned_count=len(selected),
            next_offset=returned_end if returned_end < len(matched) else None,
            capabilities=tuple(capability.compact_summary() for capability in selected),
        )


class AgentCapabilityNamespace:
    """Attribute namespace generated from declared capability ABI names."""

    def __getattr__(self, name: str) -> type[AgentCapabilityDeclaration]:
        """Resolve one generated attribute name to its declaration."""
        for declaration in agent_capability_declarations():
            if _capability_attribute_name(declaration.name) == name:
                return declaration
        raise AttributeError(f"Unknown OpenHCS agent capability attribute: {name}")

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError(f"{type(self).__name__} is immutable.")


@to_jsonable.register(AgentCapabilityDeclarationMeta)
def _jsonable_agent_capability(
    value: type[AgentCapabilityDeclaration],
) -> dict[str, object]:
    return value.as_jsonable()


@to_jsonable.register(AgentCapabilityGroup)
def _jsonable_agent_capability_group(value: AgentCapabilityGroup) -> dict[str, object]:
    return {
        "workflow_group": value.workflow_group.value,
        "title": value.title,
        "capability_names": list(value.capability_names),
        "tool_count": value.tool_count,
        "resource_count": value.resource_count,
    }


@to_jsonable.register(AgentCapabilityRegistry)
def _jsonable_agent_capability_registry(
    value: AgentCapabilityRegistry,
) -> dict[str, object]:
    return {
        "schema_version": value.schema_version,
        "surface_profile": value.surface_profile,
        "capabilities": [to_jsonable(capability) for capability in value.capabilities],
        "groups": [to_jsonable(group) for group in value.groups],
    }


TOPIC_ID_INPUT = AgentScalarInputContract("topic_id", default_value="pipeline_model")
SYMBOL_ID_INPUT = AgentScalarInputContract("symbol_id")
OPERATION_ID_INPUT = AgentScalarInputContract("operation_id")


class CapabilitiesResourceCapability(
    HostedTransportCapabilityMixin,
    DiscoveryCapability,
):
    name = "openhcs://capabilities"
    title = "OpenHCS agent capability registry"
    description = (
        "Lists the resources, tools, side effects, and extras exposed by this server."
    )
    service = "capability_registry"
    output_contract = AgentCapabilityRegistry
    invocation = AgentResourceFunctionInvocation(
        function=lambda: get_capability_registry(),
    )


class SweepViewerEndpointsCapability(DiscoveryCapability):
    name = "openhcs_sweep_viewer_endpoints"
    cli_command = "viewer-endpoints"
    title = "Sweep viewer endpoints"
    description = (
        "Sweeps the local OpenHCS IPC directory for live viewer endpoints, "
        "probes each through the viewer-window state authority, and classifies "
        "every live viewer as owned or foreign relative to this process. "
        "Dead sockets are filtered by a bind probe; non-viewer endpoint pairs "
        "(execution, UI bridge) are excluded."
    )
    service = "viewer_endpoint_discovery"
    exposition = DiscoveryCapability.exposition.refine(
        workflow_stage=CapabilityWorkflowStage.DIAGNOSTIC,
        role=CapabilityRole.DIAGNOSTIC,
    )
    data_exposure = ("viewer_endpoint_inventory",)
    output_contract = ViewerEndpointDiscoveryResult
    invocation = AgentServiceInvocation(
        service=lambda context: context.viewer_endpoint_discovery_service,
        method=lambda service: service.sweep(),
    )


class HealthCheckCapability(DiscoveryCapability):
    name = "openhcs_health_check"
    cli_command = "health"
    title = "Health check"
    description = (
        "Reports OpenHCS MCP health, installed OpenHCS version, packaged-resource "
        "readiness, server process identity, source freshness, installation-generation "
        "freshness, and the client-owned reconnect contract for stale-process "
        "diagnostics."
    )
    service = "capability_registry"
    exposition = DiscoveryCapability.exposition.refine(
        workflow_stage=CapabilityWorkflowStage.DIAGNOSTIC,
        role=CapabilityRole.DIAGNOSTIC,
    )
    data_exposure = (
        "installed_openhcs_version",
        "packaged_resource_readiness",
        "packaged_resource_paths",
        "mcp_process_identity",
        "mcp_source_freshness",
        "mcp_installation_generation",
    )
    output_contract = McpServerHealthResult
    invocation = AgentServerHealthInvocation()


class ListCapabilitiesCapability(
    HostedTransportCapabilityMixin,
    DiscoveryCapability,
):
    name = "openhcs_list_capabilities"
    title = "List capabilities"
    description = "Returns the canonical agent capability registry."
    service = "capability_registry"
    output_contract = AgentCapabilityRegistry
    invocation = AgentFunctionInvocation(
        function=lambda: get_capability_registry(),
    )


class SearchCapabilitiesCapability(
    HostedTransportCapabilityMixin,
    DiscoveryCapability,
):
    name = "openhcs_search_capabilities"
    title = "Search capabilities"
    description = (
        "Returns a bounded task-specific projection of the selected canonical "
        "capability registry. Filter by registry-owned workflow group, stage, target "
        "context, visibility, role, side effects, or free text before choosing tools."
    )
    service = "capability_registry"
    input_contract = AgentCapabilitySearchRequest
    output_contract = AgentCapabilitySearchResult
    invocation = AgentCapabilityRegistryRequestInvocation(
        method=AgentCapabilityRegistry.search,
    )


class SearchFunctionsCapability(
    HostedTransportCapabilityMixin,
    FunctionCatalogCapability,
):
    name = "openhcs_search_functions"
    cli_command = "functions"
    title = "Search processing functions"
    description = (
        "Searches the OpenHCS function registry by name, module, library, tag, "
        "or doc text. The library selector accepts either the registry library "
        "or an exact declaration-owned backend tag."
    )
    service = "function_catalog"
    input_contract = FunctionSearchRequest
    output_contract = FunctionCatalogPage
    invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: context.function_catalog,
        method=lambda service, request: service.search(
            query=request.query,
            library=request.library,
            limit=request.limit,
            compact_signatures=request.compact_signatures,
        ),
    )


class DescribeFunctionCapability(
    HostedTransportCapabilityMixin,
    FunctionCatalogCapability,
):
    name = "openhcs_describe_function"
    cli_command = "function"
    title = "Describe processing function"
    description = (
        "Returns signature, parameter, and bounded documentation details "
        "for one registry function."
    )
    service = "function_catalog"
    input_contract = FunctionDetailRequest
    output_contract = FunctionDetail
    invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: context.function_catalog,
        method=lambda service, request: service.get(
            request.function_id,
            max_doc_chars=request.max_doc_chars,
            compact_signature=request.compact_signature,
        ),
    )


class StartFunctionCatalogPreparationCapability(FunctionCatalogCapability):
    from openhcs.agent.dto.execution_connection import ExecutionConnectionSpec

    name = "openhcs_start_function_catalog_preparation"
    cli_command = "start-function-catalog-preparation"
    title = "Start catalog preparation"
    description = "Starts/coalesces existing native catalog/kernel preparation at an explicit owned port. Returns promptly with the exact process-incarnation handle; no custom source is submitted. Observe status, then register only once ready."
    service = "endpoint_function_catalog"
    mutating = True
    side_effects = ("prepares_function_catalog", "writes_declared_kernel_caches")
    input_contract = ExecutionConnectionSpec
    output_contract = FunctionCatalogPreparationState
    invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: context.endpoint_function_catalog,
        method=lambda service, request: service.start_catalog_preparation(request),
    )


class GetFunctionCatalogPreparationStatusCapability(FunctionCatalogCapability):
    name = "openhcs_get_function_catalog_preparation_status"
    cli_command = "get-function-catalog-preparation-status"
    title = "Observe catalog preparation"
    description = "Returns the existing preparation future's current state/progress promptly. Use the exact returned connection/process handle; stale owners reject without starting or replacing a runtime."
    service = "endpoint_function_catalog"
    input_contract = FunctionCatalogPreparationHandle
    output_contract = FunctionCatalogPreparationState
    invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: context.endpoint_function_catalog,
        method=lambda service, request: service.catalog_preparation_status(request),
    )


class CancelFunctionCatalogPreparationCapability(FunctionCatalogCapability):
    name = "openhcs_cancel_function_catalog_preparation"
    cli_command = "cancel-function-catalog-preparation"
    title = "Cancel owned catalog preparation"
    description = "Signals cancellation of the same incarnation-bound preparation future without blocking for child cleanup. Observe status until terminal; it does not restart preparation or submit custom source."
    service = "endpoint_function_catalog"
    mutating = True
    side_effects = ("cancels_function_catalog_preparation",)
    input_contract = FunctionCatalogPreparationHandle
    output_contract = FunctionCatalogPreparationState
    invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: context.endpoint_function_catalog,
        method=lambda service, request: service.cancel_catalog_preparation(request),
    )


class RegisterCustomFunctionCapability(FunctionCatalogCapability):
    name = "openhcs_register_custom_function"
    cli_command = "register-custom-function"
    title = "Register custom function"
    description = (
        "Validates, registers, and optionally persists custom function Python "
        "source through CustomFunctionManager, then returns registry function_id "
        "values for MCP pipeline authoring. Requires an explicit execution port; "
        "persist=true also requires the endpoint's exact storage_dir and function_name "
        "under AgentPathPolicy writable roots before dispatch. Start/observe the native "
        "catalog preparation handle first; not-ready registration rejects before source dispatch. A transport timeout "
        "is uncertain, not proof that no source or registry mutation occurred."
    )
    service = "function_catalog"
    exposition = FunctionCatalogCapability.exposition.refine(
        visibility=CapabilityVisibility.STANDARD,
    )
    mutating = True
    side_effects = ("writes_custom_function_file", "updates_function_registry")
    input_contract = CustomFunctionRegistrationRequest
    output_contract = CustomFunctionRegistrationResult
    invocation = AgentFromFieldsServiceInvocation(
        service=lambda context: context.function_catalog,
        method=lambda service, request: service.register_custom_function(request),
    )


class ObserveCustomFunctionRegistrationCapability(FunctionCatalogCapability):
    name = "openhcs_get_custom_function_registration_status"
    cli_command = "get-custom-function-registration-status"
    title = "Observe custom registration source"
    description = "Read exact publication/persistence proofs through the original native owners using observation_handle. Does not evaluate/load source or prepare a catalog. Missing evidence stays not_observed; it never authorizes registration replay or proves original mutation did not occur."
    service = "function_catalog"
    exposition = FunctionCatalogCapability.exposition.refine(
        visibility=CapabilityVisibility.STANDARD,
    )
    input_contract = CustomFunctionRegistrationHandle
    output_contract = CustomFunctionRegistrationObservation
    invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: context.function_catalog,
        method=lambda service, request: service.observe_custom_function_registration(request),
    )


class GetAuthoringContextCapability(KnowledgeCapability):
    name = "openhcs_get_authoring_context"
    cli_command = "authoring-context"
    title = "Get operating guide"
    description = (
        "Returns bounded operating guidance for choosing and completing OpenHCS workflows. "
        "Agents that do not already know OpenHCS should request kind='first_use' "
        "for a compact orientation and intent router before choosing tools, then "
        "request only the task-specific context it recommends. Reuse these operating "
        "guides when resuming work or moving to execution, diagnosis, or result review."
    )
    service = "llm_context"
    input_contract = AuthoringContextRequest
    output_contract = AuthoringContext
    invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: context.authoring_context_service,
        method=lambda service, request: service.get_bounded_authoring_context(request),
    )


class KnowledgeResourceCapability(
    HostedTransportCapabilityMixin,
    KnowledgeCapability,
):
    name = "openhcs://knowledge"
    title = "OpenHCS agent knowledge base"
    description = "Lists source-backed OpenHCS documentation available to agents."
    service = "knowledge_base"
    data_exposure = ("local_documentation_paths",)
    output_contract = KnowledgeBaseCatalog
    invocation = AgentResourceServiceInvocation(
        service=lambda context: context.knowledge_base_service,
        method=lambda service: service.list_documents(),
    )


class ListKnowledgeDocumentsCapability(
    HostedTransportCapabilityMixin,
    KnowledgeCapability,
):
    name = "openhcs_list_knowledge_documents"
    cli_command = "knowledge"
    title = "List knowledge documents"
    description = "Lists source-backed OpenHCS documentation available through the MCP knowledge base."
    service = "knowledge_base"
    data_exposure = ("local_documentation_paths",)
    output_contract = KnowledgeBaseCatalog
    invocation = AgentServiceInvocation(
        service=lambda context: context.knowledge_base_service,
        method=lambda service: service.list_documents(),
    )


class GetKnowledgeDocumentCapability(
    MainThreadProgressCapability,
    HostedTransportCapabilityMixin,
    KnowledgeCapability,
):
    name = "openhcs_get_knowledge_document"
    cli_command = "knowledge-document"
    title = "Get knowledge document"
    description = (
        "Returns one bounded allowlisted OpenHCS documentation document or section."
    )
    service = "knowledge_base"
    data_exposure = ("local_documentation_paths", "documentation_content")
    input_contract = KnowledgeBaseDocumentRequest
    output_contract = KnowledgeBaseDocument
    invocation = AgentFromFieldsServiceInvocation(
        service=lambda context: context.knowledge_base_service,
        method=lambda service, request: service.get_document(request),
    )


class SearchKnowledgeCapability(
    HostedTransportCapabilityMixin,
    KnowledgeCapability,
):
    name = "openhcs_search_knowledge"
    cli_command = "knowledge-search"
    title = "Search knowledge base"
    description = "Searches the allowlisted OpenHCS documentation knowledge base."
    service = "knowledge_base"
    data_exposure = ("local_documentation_paths", "documentation_content_snippets")
    input_contract = KnowledgeBaseSearchRequest
    output_contract = KnowledgeBaseSearchResult
    invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: context.knowledge_base_service,
        method=lambda service, request: service.search(request),
    )


class GenerateSyntheticPlateCapability(
    ProgressAcknowledgedCapability, PlatePathCapability
):
    name = "openhcs_generate_synthetic_plate"
    cli_command = "generate-synthetic-plate"
    cli_aliases = ("synthetic-plate",)
    title = "Generate synthetic plate"
    description = (
        "Generates a bounded synthetic microscopy plate using the same "
        "SyntheticMicroscopyGenerator surfaced by the UI generator window. "
        "Use it to create small multi-channel, overlapping-site fixtures "
        "before inspecting them with openhcs_inspect_plate_path."
    )
    service = "synthetic_plate_generation"
    mutating = True
    side_effects = ("writes_local_plate_files",)
    data_exposure = ("local_output_path", "generated_image_file_names")
    security_requirements = ("AgentPathPolicy writable root",)
    input_contract = SyntheticPlateGenerationRequest
    output_contract = SyntheticPlateGenerationResult
    invocation = AgentFromFieldsServiceInvocation(
        service=lambda context: context.synthetic_plate_service,
        method=lambda service, request: service.generate(request),
    )


class InspectPlatePathCapability(ProgressAcknowledgedCapability, PlatePathCapability):
    progress_worker_thread_safe = True
    name = "openhcs_inspect_plate_path"
    cli_command = "inspect-plate"
    title = "Inspect plate path"
    description = (
        "Diagnostic-only, read-only inspection of a local plate folder: microscope handler "
        "detection, microscope metadata, image-file samples, filename parse "
        "coverage, registry-derived format-specific candidate evidence, "
        "workspace-preparation advice, and structured workflow routing. "
        "It does not configure a running UI or make a handler override the setup "
        "route; use the PlateManager code document plus selected-plate init when "
        "the result must remain visible in the desktop. Optional Bio-Formats "
        "cold preparation can download verified Fiji artifacts into its declared "
        "bundle cache and start Java; progress keeps this operation observable "
        "without blocking unrelated MCP reads. Plate contents remain read-only."
    )
    service = "selected_plate"
    mutating = True
    side_effects = (
        "may_download_verified_fiji_runtime",
        "may_write_runtime_bundle_cache",
        "may_start_java_runtime",
    )
    data_exposure = (
        "local_plate_path",
        "microscope_metadata",
        "image_file_names",
        "result_artifact_names",
        "filename_parse_summaries",
    )
    security_requirements = ("AgentPathPolicy readable root",)
    input_contract = PlatePathInspectionRequest
    output_contract = PlatePathInspectionResult
    invocation = AgentFromFieldsServiceInvocation(
        service=lambda context: context.plate_inspection_service,
        method=lambda service, request: service.inspect(request),
    )


class QueryPlateFilesCapability(MainThreadProgressCapability, PlatePathCapability):
    name = "openhcs_query_plate_files"
    cli_command = "query-plate-files"
    title = "Query plate files"
    description = (
        "Read-only query of image/result file records exposed "
        "by a local plate inventory. Returns virtual image names, source "
        "paths, result artifact paths, and metadata from the same inventory "
        "API used by the Image Browser. For retained outputs outside the standard "
        "plate layout, pass result_directory with kind='result'. This inspects "
        "persisted files and bounded native previews without microscope detection "
        "or inferred acquisition identity; it does not attest writer success."
    )
    service = "plate_inspection"
    data_exposure = (
        "local_plate_path",
        "plate_virtual_image_path",
        "plate_source_image_path",
        "result_artifact_names",
        "file_metadata",
    )
    security_requirements = ("AgentPathPolicy readable root",)
    input_contract = PlateFileQueryRequest
    output_contract = PlateFileQueryResult
    invocation = AgentFromFieldsServiceInvocation(
        service=lambda context: context.plate_inspection_service,
        method=lambda service, request: service.query_files(request),
    )


class SamplePlateImageCapability(MainThreadProgressCapability, PlatePathCapability):
    name = "openhcs_sample_plate_image"
    cli_command = "sample-plate-image"
    title = "Sample plate image"
    description = (
        "Resolves a plate image by virtual/source path, full virtual path, "
        "or unique basename, then reads bounded pixels from a native-resolution "
        "region and returns its statistics scope, source/resolution shapes, selected "
        "resolution, and downsampling provenance. Omit resolution_index for safe "
        "automatic selection or pass 0 for exact full-resolution pixels."
    )
    service = "plate_inspection"
    data_exposure = (
        "local_plate_path",
        "plate_virtual_image_path",
        "plate_source_image_path",
        "bounded_image_pixels",
    )
    security_requirements = ("AgentPathPolicy readable root",)
    input_contract = PlateImageSampleRequest
    output_contract = PlateImageSampleResult
    invocation = AgentFromFieldsServiceInvocation(
        service=lambda context: context.plate_inspection_service,
        method=lambda service, request: service.sample_image(request),
    )


class StreamPlateFilesToViewerCapability(MainThreadProgressCapability, PlatePathCapability):
    name = "openhcs_stream_plate_files_to_viewer"
    cli_command = "stream-plate-files"
    title = "Stream plate files to viewer"
    description = (
        "Resolves image or ROI result records by virtual path, source path, "
        "result path, basename, or bounded inventory query, then streams them "
        "to a managed viewer through the same core service used by the Image Browser."
        " Set result_directory to reopen retained native results independently of "
        "their output location; plate_path supplies the original source context. "
        "ROI reopening requires persisted source metadata, not filename guesses."
    )
    service = "plate_streaming"
    mutating = True
    side_effects = ("launches_or_updates_managed_viewer",)
    data_exposure = (
        "local_plate_path",
        "plate_virtual_image_path",
        "plate_source_image_path",
        "result_artifact_names",
        "viewer_connection",
    )
    runtime_requirements = ("napari_or_fiji_viewer_runtime",)
    required_extras = ("viz",)
    security_requirements = ("AgentPathPolicy readable root",)
    input_contract = PlateFileStreamRequest
    output_contract = PlateFileStreamResult
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.plate_streaming_service,
        method=lambda service, request, connection: service.stream_files(
            request, ui_bridge_connection=connection
        ),
    )


class UiInspectSelectedPlateImagesCapability(UiSelectedPlateCapability):
    name = "openhcs_ui_inspect_selected_plate_images"
    cli_command = "selected-plate-images"
    title = "Inspect selected plate images"
    description = (
        "Reads the current PlateManager selection from the running UI bridge, "
        "requires exactly one selected plate, resolves the selected, source, "
        "or output plate target, then returns the same read-only image inventory "
        "and microscope metadata produced by openhcs_inspect_plate_path."
    )
    service = "plate_inspection"
    data_exposure = (
        "ui_selected_plate_path",
        "microscope_metadata",
        "image_file_names",
        "result_artifact_names",
        "filename_parse_summaries",
    )
    runtime_requirements = ("running_openhcs_ui_bridge",)
    security_requirements = ("ui_bridge_auth_token", "AgentPathPolicy readable root")
    input_contract = SelectedPlateImageInspectionRequest
    output_contract = SelectedPlateImageInspectionResult
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.selected_plate_service,
        method=lambda service, request, connection: service.inspect_images(
            request,
            connection,
        ),
    )


class UiQuerySelectedPlateFilesCapability(UiSelectedPlateCapability):
    name = "openhcs_ui_query_selected_plate_files"
    cli_command = "selected-plate-files"
    title = "Query selected plate files"
    description = (
        "Reads the current PlateManager selection from the running UI bridge, "
        "requires exactly one selected plate, then returns the same image/result "
        "file records produced by openhcs_query_plate_files."
    )
    service = "selected_plate"
    data_exposure = (
        "ui_selected_plate_path",
        "plate_virtual_image_path",
        "plate_source_image_path",
        "result_artifact_names",
        "file_metadata",
    )
    runtime_requirements = ("running_openhcs_ui_bridge",)
    security_requirements = ("ui_bridge_auth_token", "AgentPathPolicy readable root")
    input_contract = SelectedPlateFileQueryRequest
    output_contract = SelectedPlateFileQueryResult
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.selected_plate_service,
        method=lambda service, request, connection: service.query_files(
            request,
            connection,
        ),
    )


class UiSampleSelectedPlateImageCapability(UiSelectedPlateCapability):
    name = "openhcs_ui_sample_selected_plate_image"
    cli_command = "selected-plate-sample"
    title = "Sample selected plate image"
    description = (
        "Sample a selected-plate image after reading the current PlateManager "
        "selection from the running UI bridge, "
        "then reads a bounded native-resolution region from a selected/source/output "
        "plate image by virtual/source path. Omit resolution_index for safe automatic "
        "selection or pass 0 for exact full-resolution pixels. If no "
        "image_path is supplied, it deterministically samples the first image "
        "reported by openhcs_inspect_plate_path."
    )
    service = "selected_plate"
    data_exposure = (
        "ui_selected_plate_path",
        "plate_virtual_image_path",
        "plate_source_image_path",
        "bounded_image_pixels",
    )
    runtime_requirements = ("running_openhcs_ui_bridge",)
    security_requirements = ("ui_bridge_auth_token", "AgentPathPolicy readable root")
    input_contract = SelectedPlateImageSampleRequest
    output_contract = SelectedPlateImageSampleResult
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.selected_plate_service,
        method=lambda service, request, connection: service.sample_image(
            request,
            connection,
        ),
    )


class UiStreamSelectedPlateFilesToViewerCapability(MainThreadProgressCapability, UiSelectedPlateCapability):
    name = "openhcs_ui_stream_selected_plate_files_to_viewer"
    cli_command = "selected-plate-stream"
    title = "Stream selected plate files to viewer"
    description = (
        "Reads the current PlateManager selection from the running UI bridge, "
        "resolves selected/source/output image or ROI records through the same "
        "inventory API as openhcs_ui_query_selected_plate_files, then streams "
        "them to a managed viewer."
    )
    service = "selected_plate"
    data_exposure = (
        "ui_selected_plate_path",
        "plate_virtual_image_path",
        "plate_source_image_path",
        "result_artifact_names",
        "viewer_connection",
    )
    runtime_requirements = (
        "running_openhcs_ui_bridge",
        "napari_or_fiji_viewer_runtime",
    )
    required_extras = ("viz",)
    security_requirements = ("ui_bridge_auth_token", "AgentPathPolicy readable root")
    input_contract = SelectedPlateFileStreamRequest
    output_contract = SelectedPlateFileStreamResult
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.selected_plate_service,
        method=lambda service, request, connection: service.stream_files(
            request,
            connection,
        ),
    )


class ArchitectureTopicsResourceCapability(ArchitectureCapability):
    name = "openhcs://architecture/topics"
    title = "Architecture topics"
    description = (
        "Lists read-only architecture topics backed by real OpenHCS internal symbols."
    )
    service = "architecture_projection"
    output_contract = ArchitectureTopicPage
    invocation = AgentResourceServiceInvocation(
        service=lambda context: context.architecture_service,
        method=lambda service: service.list_topics(),
    )


class ListArchitectureTopicsCapability(ArchitectureCapability):
    name = "openhcs_list_architecture_topics"
    cli_command = "architecture"
    title = "List architecture topics"
    description = "Lists architecture topics available to agents."
    service = "architecture_projection"
    output_contract = ArchitectureTopicPage
    invocation = AgentServiceInvocation(
        service=lambda context: context.architecture_service,
        method=lambda service: service.list_topics(),
    )


class ExplainArchitectureCapability(ArchitectureCapability):
    name = "openhcs_explain_architecture"
    cli_command = "architecture-topic"
    cli_aliases = ("explain-architecture",)
    title = "Explain architecture topic"
    description = "Explains one OpenHCS architecture topic using source-backed internal API symbols."
    service = "architecture_projection"
    input_contract = TOPIC_ID_INPUT
    output_contract = ArchitectureTopic
    invocation = AgentScalarServiceInvocation(
        service=lambda context: context.architecture_service,
        method=lambda service, value: service.explain_topic(value),
    )


class DescribeInternalSymbolCapability(ArchitectureCapability):
    name = "openhcs_describe_internal_symbol"
    cli_command = "internal-symbol"
    cli_aliases = ("architecture-symbol",)
    title = "Describe internal symbol"
    description = (
        "Returns read-only signature/doc/source-location facts for one symbol_id "
        "exposed by the curated architecture topics. Discover topic_ids with "
        f"{ListArchitectureTopicsCapability.name}, then inspect their symbol_ids "
        f"with {ExplainArchitectureCapability.name}; arbitrary Python import paths "
        "are not accepted."
    )
    service = "architecture_projection"
    input_contract = SYMBOL_ID_INPUT
    output_contract = InternalApiSymbol
    invocation = AgentScalarServiceInvocation(
        service=lambda context: context.architecture_service,
        method=lambda service, value: service.describe_internal_symbol(value),
    )


class DescribeConfigSchemaCapability(
    HostedTransportCapabilityMixin,
    ConfigDraftCapability,
):
    name = "openhcs_describe_config_schema"
    cli_command = "config-schema"
    title = "Describe configuration schema"
    description = (
        "Reflects GlobalPipelineConfig, PipelineConfig, the FunctionStep config "
        "override surface, or read-only UIConfig without materializing lazy values. "
        "With no path_prefix it returns the top-level owner-derived map; pass a "
        "returned nested_schema_path to retrieve that subtree. Field path is for "
        "schema navigation; authoring_value_path gives the exact nested JSON "
        "object/list route accepted by the owning mutation boundary. Use "
        "config_type='step' for exact "
        "FunctionStepAddRequest.step_config_overrides structure. UIConfig fields "
        "are authored through the live UI ObjectState, not ConfigPatch."
    )
    service = "config"
    input_contract = ConfigSchemaRequest
    output_contract = ConfigSchema
    invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: context.config_service,
        method=lambda service, request: service.describe_schema_request(request),
    )


class CreateConfigCapability(ConfigDraftCapability):
    name = "openhcs_create_config"
    title = "Create configuration"
    description = "Creates a draft config reference from a typed config patch."
    service = "config"
    mutating = True
    side_effects = ("creates_in_memory_config_ref",)
    input_contract = ConfigPatch
    output_contract = ConfigRef
    invocation = AgentConfigPatchServiceInvocation(
        service=lambda context: context.config_service,
        method=lambda service, request: service.create(
            request.config_type,
            request,
        ),
    )


class ValidateConfigPatchCapability(ConfigDraftCapability):
    name = "openhcs_validate_config_patch"
    title = "Validate configuration patch"
    description = (
        "Validates that a config patch can instantiate the target OpenHCS config class."
    )
    service = "config"
    exposition = ConfigDraftCapability.exposition.refine(
        workflow_stage=CapabilityWorkflowStage.VALIDATION,
    )
    input_contract = ConfigPatch
    output_contract = ConfigValidationResult
    invocation = AgentConfigPatchServiceInvocation(
        service=lambda context: context.config_service,
        method=lambda service, request: service.validate_patch(
            request.config_type,
            request,
        ),
    )


class RenderConfigSourceCapability(ConfigDraftCapability):
    name = "openhcs_render_config_source"
    title = "Render configuration source"
    description = "Renders a draft config reference as Python source using OpenHCS pycodify formatters."
    service = "config"
    input_contract = ConfigSourceRenderRequest
    output_contract = RenderedSource
    invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: context.config_service,
        method=lambda service, request: service.render_source(
            request.config_id,
            clean=request.clean,
        ),
    )


class CreatePipelineCapability(PipelineDraftCapability):
    name = "openhcs_create_pipeline"
    title = "Create draft pipeline"
    description = (
        "Creates an in-memory agent-authored OpenHCS pipeline document, using "
        "the referenced PipelineConfig or a new default PipelineConfig."
    )
    service = "pipeline_authoring"
    mutating = True
    side_effects = ("creates_in_memory_pipeline_ref",)
    output_contract = PipelineRef
    input_contract = CreatePipelineRequest
    invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: context.pipeline_service,
        method=lambda service, request: service.create_pipeline_from_request(request),
    )


class AddFunctionStepCapability(PipelineDraftCapability):
    name = "openhcs_add_function_step"
    title = "Add FunctionStep"
    description = (
        "Adds a FunctionStepSpec resolved through the OpenHCS function registry."
    )
    service = "pipeline_authoring"
    mutating = True
    side_effects = ("mutates_in_memory_pipeline_ref",)
    input_contract = FunctionStepAddRequest
    output_contract = PipelineSpec
    invocation = AgentFromFieldsServiceInvocation(
        service=lambda context: context.pipeline_service,
        method=lambda service, request: service.add_function_step_from_request(request),
    )


class ValidatePipelineCapability(PipelineDraftCapability):
    name = "openhcs_validate_pipeline"
    title = "Validate draft pipeline"
    description = (
        "Validates function references and constructs the complete OpenHCS "
        "PipelineDocument owned by the draft."
    )
    service = "pipeline_authoring"
    exposition = PipelineDraftCapability.exposition.refine(
        workflow_stage=CapabilityWorkflowStage.VALIDATION,
    )
    input_contract = PipelineValidationRequest
    output_contract = PipelineValidationResult
    invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: context.pipeline_service,
        method=lambda service, request: service.validate(request.pipeline_id),
    )


class RenderPipelineSourceCapability(PipelineDraftCapability):
    name = "openhcs_render_pipeline_source"
    title = "Render pipeline source"
    description = (
        "Renders an authored PipelineDocument as Python source containing its "
        "PipelineConfig and FunctionStep declarations."
    )
    service = "pipeline_authoring"
    input_contract = PipelineSourceRenderRequest
    output_contract = RenderedSource
    invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: context.pipeline_service,
        method=lambda service, request: service.render_source(
            request.pipeline_id,
            clean=request.clean,
        ),
    )


class CreateOrchestratorSessionCapability(HeadlessExecutionCapability):
    name = "openhcs_create_orchestrator_session"
    title = "Create orchestrator session"
    description = (
        "Creates an opaque headless execution session from a plate path and "
        "the complete PipelineDocument owned by a pipeline draft. Use the UI "
        "PlateManager code document and "
        "selected-plate workflow instead when an open UI should show the work."
    )
    service = "execution_session"
    mutating = True
    side_effects = ("creates_in_memory_execution_session",)
    input_contract = OrchestratorSessionCreationRequest
    output_contract = OrchestratorSessionRef
    invocation = AgentFromFieldsServiceInvocation(
        service=lambda context: context.execution_service,
        method=lambda service, request: service.create_session_from_request(request),
    )


class CreateOrchestratorSessionFromPipelineSourceCapability(
    MainThreadProgressCapability, HeadlessExecutionCapability
):
    name = "openhcs_create_orchestrator_session_from_pipeline_source"
    title = "Create source-backed orchestrator session"
    description = (
        "Creates an opaque headless execution session from an exact pycodified "
        "PipelineDocument containing pipeline_steps and an optional "
        "pipeline_config, whose omission selects PipelineConfig(), such as "
        "Pipeline Editor code-mode content. An optional execution_plate_path "
        "selects a prepared input workspace while plate_path retains the "
        "original source identity. A PlateManager document is a "
        "multi-plate aggregate, not pipeline source; use the UI selected-plate "
        "workflow when an open UI should show rows, snapshots, and output auto-add."
    )
    service = "execution_session"
    mutating = True
    side_effects = ("creates_in_memory_execution_session",)
    input_contract = PipelineSourceOrchestratorSessionRequest
    output_contract = OrchestratorSessionRef
    invocation = AgentFromFieldsServiceInvocation(
        service=lambda context: context.execution_service,
        method=lambda service, request: (
            service.create_session_from_pipeline_source_request(request)
        ),
    )


class GetOrchestratorSessionCapability(HeadlessExecutionCapability):
    name = "openhcs_get_orchestrator_session"
    title = "Get orchestrator session"
    description = "Returns the stored plate, pipeline, config, and ZMQ connection identity for a session."
    service = "execution_session"
    input_contract = OrchestratorSessionRequest
    output_contract = OrchestratorSession
    invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: context.execution_service,
        method=lambda service, request: service.get_session_from_request(request),
    )


class InspectPipelineSourceArtifactPlanCapability(
    MainThreadProgressCapability, PipelineDraftCapability
):
    name = "openhcs_inspect_pipeline_source_artifact_plan"
    cli_command = "artifact-plan"
    title = "Inspect source artifact plan"
    description = (
        "Compiles a complete pycodified PipelineDocument with an explicit progress queue "
        "and returns bounded axis, step, group-key, virtual source-workspace, "
        "path, main-flow checkpoint, viewer-streaming, and artifact-output plans."
        " Initialization may persist workspace metadata; the plate must be under "
        "an authorized write root. Use an explicitly staged writable plate when "
        "preserving read-only originals."
        f" Source workspace: {getdoc(SourceWorkspaceSummary)}"
    )
    service = "execution_session"
    mutating = True
    side_effects = ("may_persist_workspace_metadata",)
    exposition = PipelineDraftCapability.exposition.refine(
        workflow_stage=CapabilityWorkflowStage.VALIDATION,
    )
    input_contract = PipelineSourceArtifactPlanInspectionRequest
    output_contract = ArtifactPlanInspection
    invocation = AgentFromFieldsServiceInvocation(
        service=lambda context: context.execution_service,
        method=lambda service, request: (
            service.inspect_pipeline_source_artifact_plan_request(request)
        ),
    )


class SubmitCompileCapability(ProgressAcknowledgedCapability, HeadlessExecutionCapability):
    name = "openhcs_submit_compile"
    title = "Submit compile job"
    description = (
        "Submits a compile-only ZMQ execution job for an execution session. "
        "Use wait=False for normal agent workflows, then poll status by job_id; "
        "submit is bounded by submit_timeout_ms and wait=True is bounded by "
        "wait_timeout_ms."
    )
    service = "execution_session"
    mutating = True
    side_effects = ("submits_zmq_compile_job",)
    input_contract = CompileSubmissionRequest
    output_contract = AgentResultFamilyContract(
        ExecutionJobRef, ExecutionSessionService._submit_job
    )
    invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: context.execution_service,
        method=lambda service, request: service.submit_compile(
            request.session_id,
            wait=request.wait,
            submit_timeout_ms=request.submit_timeout_ms,
            wait_timeout_ms=request.wait_timeout_ms,
        ),
    )


class SubmitPipelineExecutionCapability(
    ProgressAcknowledgedCapability, HeadlessExecutionCapability
):
    name = "openhcs_submit_pipeline_execution"
    title = "Submit pipeline execution"
    description = (
        "Submits a headless ZMQ pipeline execution job for an execution session. "
        "Use wait=False for normal agent workflows, then poll status by job_id; "
        "submit is bounded by submit_timeout_ms and wait=True is bounded by "
        "wait_timeout_ms. An optional runtime observation export path must be "
        "writable under the agent path policy. The optional observation scope "
        "selects full runtime values or outcome-only evidence without retaining "
        "array values. This path does not update the "
        "running UI PlateManager; "
        "use openhcs_ui_selected_plate_workflow for user-visible UI runs."
    )
    service = "execution_session"
    mutating = True
    side_effects = ("submits_zmq_execution_job",)
    input_contract = PipelineExecutionSubmissionRequest
    output_contract = AgentResultFamilyContract(
        ExecutionJobRef, ExecutionSessionService._submit_job
    )
    invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: context.execution_service,
        method=lambda service, request: service.submit_execution(
            request.session_id,
            compile_artifact_id=request.compile_artifact_id,
            runtime_observation_export_path=request.runtime_observation_export_path,
            runtime_observation_export_scope=request.runtime_observation_export_scope,
            wait=request.wait,
            submit_timeout_ms=request.submit_timeout_ms,
            wait_timeout_ms=request.wait_timeout_ms,
        ),
    )


class GetExecutionStatusCapability(SubmittedJobCapability):
    name = "openhcs_get_execution_status"
    title = "Get execution status"
    description = (
        "Polls one submitted ZMQ job and returns its lifecycle status plus the "
        "submitting client's latest exact progress observation."
    )
    service = "execution_session"
    input_contract = ExecutionStatusRequest
    output_contract = ExecutionJobStatus
    invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: context.execution_service,
        method=lambda service, request: service.get_job_status(
            request.job_id,
            timeout_ms=request.timeout_ms,
        ),
    )


class CancelExecutionCapability(HeadlessExecutionCapability):
    name = "openhcs_cancel_execution"
    title = "Cancel execution job"
    description = (
        "Requests cancellation of one submitted compile or pipeline job through "
        "its ordinary execution server. Returns whether cancellation was applied "
        "and the job status observed afterward."
    )
    service = "execution_session"
    mutating = True
    side_effects = ("requests_zmq_execution_cancellation",)
    exposition = HeadlessExecutionCapability.exposition.refine(
        workflow_stage=CapabilityWorkflowStage.CONTROL,
        target_context=CapabilityTargetContext.SUBMITTED_JOB,
    )
    input_contract = ExecutionCancellationRequest
    output_contract = ExecutionJobCancellationResult
    invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: context.execution_service,
        method=lambda service, request: service.cancel_job(
            request.job_id,
            timeout_ms=request.timeout_ms,
        ),
    )


class StartOwnedRuntimeCapability(RuntimeServerCapability):
    name = "openhcs_start_owned_runtime"
    cli_command = "runtime-start-owned"
    title = "Start owned execution runtime"
    description = "Explicitly spawn once at an empty local execution pair after native write admission. Returns the exact child handle promptly, without catalogue warming or adopting/replacing any endpoint. Never replay an uncertain startup."
    service = "runtime_server"
    mutating = True
    side_effects = ("spawns_owned_execution_runtime", "writes_native_startup_artifacts")
    exposition = RuntimeServerCapability.exposition.refine(
        workflow_group=CapabilityWorkflowGroup.FUNCTION_AUTHORING,
        visibility=CapabilityVisibility.STANDARD,
        role=CapabilityRole.PRIMARY,
        workflow_stage=CapabilityWorkflowStage.CONTROL,
    )
    input_contract = RuntimeBootstrapStartRequest
    output_contract = RuntimeBootstrapState
    invocation = AgentFromFieldsServiceInvocation(
        service=lambda context: context.runtime_server_service,
        method=lambda service, request: service.start_from_request(request),
    )


class ObserveOwnedRuntimeCapability(RuntimeServerCapability):
    name = "openhcs_observe_owned_runtime"
    title = "Observe owned runtime startup"
    description = "Read startup activity and readiness of the exact spawned child handle. No spawn, replacement, catalogue warming, or mutation. Preserve pending/uncertain handles."
    service = "runtime_server"
    input_contract = RuntimeBootstrapObserveRequest
    output_contract = RuntimeBootstrapState
    exposition = StartOwnedRuntimeCapability.exposition.refine(
        workflow_stage=CapabilityWorkflowStage.STATUS
    )
    invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: context.runtime_server_service,
        method=lambda service, request: service.observe_bootstrap(request),
    )


class CloseOwnedRuntimeCapability(RuntimeServerCapability):
    name = "openhcs_close_owned_runtime"
    title = "Close exact owned execution runtime"
    description = "Close only the retained bootstrap child proven by both native endpoint reservations. FORCE sends at most one shutdown request and closes through the exact process owner within the existing budget; listener disappearance is not process exit. GRACEFUL clears workers but keeps the server. Retain unresolved handles and observe without replay."
    service = "runtime_server"
    mutating = True
    side_effects = ("requests_owned_runtime_shutdown", "terminates_exact_owned_process")
    exposition = StartOwnedRuntimeCapability.exposition
    input_contract = RuntimeBootstrapCloseRequest
    output_contract = RuntimeBootstrapCloseResult
    invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: context.runtime_server_service,
        method=lambda service, request: service.close_bootstrap(request),
    )


class ScanRuntimeServersCapability(RuntimeServerCapability):
    name = "openhcs_scan_runtime_servers"
    cli_command = "runtime-scan"
    title = "Scan runtime servers"
    description = "Scans candidate ports for running OpenHCS ZMQ execution servers."
    service = "runtime_server"
    input_contract = RuntimeServerScanRequest
    output_contract = RuntimeServerScanResult
    invocation = AgentFromFieldsServiceInvocation(
        service=lambda context: context.runtime_server_service,
        method=lambda service, request: service.scan_from_request(request),
    )


class GetRuntimeServerInfoCapability(RuntimeServerCapability):
    name = "openhcs_get_runtime_server_info"
    cli_command = "runtime-info"
    title = "Get runtime server info"
    description = "Returns a read-only server snapshot from a running OpenHCS ZMQ execution server."
    service = "runtime_server"
    input_contract = RuntimeServerInfoRequest
    output_contract = RuntimeServerInfo
    invocation = AgentFromFieldsServiceInvocation(
        service=lambda context: context.runtime_server_service,
        method=lambda service, request: service.server_info_from_request(request),
    )


class GetRuntimeServerExecutionStatusCapability(RuntimeServerCapability):
    name = "openhcs_get_runtime_server_execution_status"
    cli_command = "runtime-status"
    title = "Get runtime execution status"
    description = "Returns a bounded execution-status projection from a running OpenHCS runtime server."
    service = "runtime_server"
    input_contract = RuntimeServerExecutionStatusRequest
    output_contract = RuntimeExecutionStatus
    invocation = AgentFromFieldsServiceInvocation(
        service=lambda context: context.runtime_server_service,
        method=lambda service, request: service.execution_status_from_request(request),
    )


class InspectDebugRuntimeValuesCapability(RuntimeServerCapability):
    name = "openhcs_inspect_debug_runtime_values"
    cli_command = "runtime-debug-values"
    title = "Inspect paused runtime values"
    description = (
        "Returns the renderer-independent artifact keys, storage locations, and "
        "value types visible in one paused OpenHCS debug worker."
    )
    service = "runtime_server"
    runtime_requirements = (
        "running_openhcs_execution_server",
        "paused_debug_session",
    )
    data_exposure = (
        "runtime_artifact_keys",
        "runtime_artifact_storage_locations",
        "runtime_value_types",
    )
    input_contract = RuntimeDebugInspectionRequest
    output_contract = RuntimeDebugInspectionResult
    invocation = AgentFromFieldsServiceInvocation(
        service=lambda context: context.runtime_server_service,
        method=lambda service, request: service.runtime_debug_inspection_from_request(
            request
        ),
    )


class SendDebugCommandCapability(RuntimeServerCapability):
    name = "openhcs_send_debug_command"
    cli_command = "runtime-debug-command"
    title = "Send debug worker command"
    description = (
        "Sends one DebugWorkerCommandRequest command type (toggle, step, run, "
        "run_to_pause, restart, choose_source_group, random_source_group, stop) "
        "to a paused OpenHCS debug worker and returns the resulting worker "
        "status. Fails closed against the DebugCommandType authority."
    )
    service = "runtime_server"
    mutating = True
    side_effects = ("mutates_debug_worker_state",)
    runtime_requirements = (
        "running_openhcs_execution_server",
        "paused_debug_session",
    )
    data_exposure = ("runtime_debug_worker_status",)
    input_contract = RuntimeDebugCommandRequest
    output_contract = RuntimeDebugCommandResult
    invocation = AgentFromFieldsServiceInvocation(
        service=lambda context: context.runtime_server_service,
        method=lambda service, request: service.debug_command_from_request(request),
    )


class ExportDebugArtifactCapability(RuntimeServerCapability):
    name = "openhcs_export_debug_artifact"
    cli_command = "runtime-debug-export"
    title = "Export debug artifact"
    description = (
        "Requests server-side export/materialization of one artifact ref "
        "reported by runtime-debug-values into a writable agent root, and "
        "returns the exported reference. The export root is validated against "
        "the agent path-policy writable roots before the request is issued."
    )
    service = "runtime_server"
    mutating = True
    side_effects = ("writes_debug_artifact_export",)
    runtime_requirements = (
        "running_openhcs_execution_server",
        "paused_debug_session",
    )
    data_exposure = ("runtime_artifact_export",)
    input_contract = RuntimeDebugArtifactExportRequest
    output_contract = RuntimeDebugArtifactExportResult
    invocation = AgentFromFieldsServiceInvocation(
        service=lambda context: context.runtime_server_service,
        method=lambda service, request: service.debug_artifact_export_from_request(
            request
        ),
    )


class ViewerSnapshotWindowCapability(ViewerWindowCapability):
    name = "openhcs_viewer_snapshot_window"
    cli_command = "snapshot-viewer"
    title = "Snapshot viewer window"
    description = "Captures a running OpenHCS viewer window, such as Napari, through its ZMQ control socket."
    service = "viewer_window"
    mutating = True
    side_effects = ("writes_agent_output_file",)
    runtime_requirements = ("running_openhcs_viewer_server",)
    data_exposure = ("viewer_screenshot", "local_output_path")
    security_requirements = ("agent_path_policy",)
    input_contract = ViewerWindowSnapshotRequest
    output_contract = ViewerWindowSnapshotResult
    invocation = AgentViewerWindowRequestServiceInvocation(
        service=lambda context: context.viewer_window_service,
        method=lambda service, request: service.snapshot_window(request),
    )


class CloseViewerWindowCapability(ViewerWindowCapability):
    name = "openhcs_close_viewer_window"
    title = "Close viewer window"
    description = (
        "Closes one explicitly selected running viewer through its declared ZMQ "
        "lifecycle endpoint and verifies that the viewer process terminates. "
        "Requires confirmed=true."
    )
    service = "viewer_window"
    mutating = True
    side_effects = ("closes_viewer_window", "terminates_viewer_process")
    runtime_requirements = ("running_openhcs_viewer_server",)
    security_requirements = ("explicit_user_confirmation",)
    input_contract = ViewerWindowCloseRequest
    output_contract = EndpointShutdownResult
    exposition = ViewerWindowCapability.exposition.refine(
        workflow_stage=CapabilityWorkflowStage.CONTROL,
        role=CapabilityRole.EXPERT,
    )
    invocation = AgentViewerWindowRequestServiceInvocation(
        service=lambda context: context.viewer_window_service,
        method=lambda service, request: service.close_window(request),
    )


class GetViewerWindowStateCapability(ViewerWindowCapability):
    name = "openhcs_get_viewer_window_state"
    cli_command = "viewer-state"
    title = "Get viewer window state"
    description = (
        "Returns bounded structured layer, component, axis, payload-summary, and "
        "shape-bound state from a running OpenHCS viewer through its ZMQ "
        "control socket."
    )
    service = "viewer_window"
    runtime_requirements = ("running_openhcs_viewer_server",)
    data_exposure = (
        "viewer_layer_state",
        "viewer_axis_state",
        "viewer_payload_summaries",
        "viewer_shape_bounds",
    )
    input_contract = ViewerWindowStateRequest
    output_contract = ViewerWindowStateResult
    invocation = AgentViewerWindowRequestServiceInvocation(
        service=lambda context: context.viewer_window_service,
        method=lambda service, request: service.window_state(request),
    )


class GetViewerWindowPayloadsCapability(ViewerWindowCapability):
    name = "openhcs_get_viewer_window_payloads"
    cli_command = "viewer-payloads"
    title = "Get viewer window payloads"
    description = (
        "Returns bounded per-layer, per-axis image and shape payload records, "
        "including exact optional arrays and shapes, from a running viewer "
        "control endpoint. Array values are omitted by default: explicitly set "
        "include_array_values=true with a sufficient max_array_elements, or use "
        "the image-sampling capability for bounded tiles."
    )
    service = "viewer_window"
    runtime_requirements = ("running_openhcs_viewer_server",)
    data_exposure = (
        "viewer_payload_records",
        "viewer_axis_coordinates",
        "viewer_shape_payloads",
        "viewer_array_values",
    )
    input_contract = ViewerWindowPayloadRequest
    output_contract = ViewerWindowPayloadResult
    invocation = AgentViewerWindowRequestServiceInvocation(
        service=lambda context: context.viewer_window_service,
        method=lambda service, request: service.window_payloads(request),
    )


class MeasureViewerPolylineCapability(ViewerWindowCapability):
    name = "openhcs_measure_viewer_polyline"
    title = "Measure native viewer polyline and intensity profile"
    description = (
        "Read-only bounded source-native (y,x) ruler/polyline with exact route and route-local axis_indices. "
        "Returns data/pixel length versus chord, transformed world geometry and endpoint-inclusive raw intensity "
        "profile. line_width uses a centred perpendicular band reduced by mean; interpolation_order0 nearest/1 bilinear. "
        "Requires one scalar2D original plane; rejects ambiguous/sparse-padding/OOB geometry before interpolation. "
        "Does not alter pixels, contrast, layers, axes or camera; world scale/units are not verified physical calibration."
    )
    service = "viewer_window"
    runtime_requirements = ("running_openhcs_napari_viewer_server",)
    data_exposure = (
        "viewer_native_measurements",
        "viewer_source_coordinates",
        "bounded_raw_intensity_profile",
    )
    input_contract = ViewerWindowPolylineMeasurementRequest
    output_contract = ViewerWindowPolylineMeasurementResult
    invocation = AgentViewerWindowRequestServiceInvocation(
        service=lambda context: context.viewer_window_service,
        method=lambda service, request: service.measure_polyline(request),
    )


class MeasureViewerRegionCapability(ViewerWindowCapability):
    name = "openhcs_measure_viewer_region"
    title = "Measure independent native region and background support"
    description = (
        "Read-only bounded independent simple polygon on one exact scalar2D original image route/axis coordinate. "
        "Returns continuous polygon and raster pixel-centre area/extent/roundness, actual transformed world geometry, "
        "raw intensity statistics and optional separately authored non-overlapping background polygon. "
        "Support is raw value strictly greater than support_threshold, or background mean + background_sigma*population std. "
        "This region is NOT a biological mask; world scale1 is not proof of micrometres. "
        "Rejects nonfinite, ambiguous, invalid axes, padding/OOB or pixel/work-budget excess before allocating masks."
    )
    service = "viewer_window"
    runtime_requirements = ("running_openhcs_napari_viewer_server",)
    data_exposure = (
        "viewer_native_measurements",
        "viewer_source_coordinates",
        "bounded_raw_intensity_statistics",
    )
    input_contract = ViewerWindowRegionMeasurementRequest
    output_contract = ViewerWindowRegionMeasurementResult
    invocation = AgentViewerWindowRequestServiceInvocation(
        service=lambda context: context.viewer_window_service,
        method=lambda service, request: service.measure_region(request),
    )


class SampleViewerWindowImageCapability(ViewerWindowCapability):
    name = "openhcs_sample_viewer_window_image"
    cli_command = "sample-viewer-image"
    title = "Sample viewer image payload"
    description = (
        "Returns native-resolution bounded image records and bounded pixel samples "
        "for routed image payloads from a running viewer control endpoint. Pixel "
        "values are omitted by default: set include_array_values=true and keep "
        "height*width within max_array_elements; tile a field when exact pixels "
        "are needed beyond that bound."
    )
    service = "viewer_window"
    runtime_requirements = ("running_openhcs_viewer_server",)
    data_exposure = (
        "viewer_payload_records",
        "viewer_axis_coordinates",
        "viewer_array_values",
    )
    input_contract = ViewerWindowImageSampleRequest
    output_contract = ViewerWindowImageSampleResult
    invocation = AgentViewerWindowRequestServiceInvocation(
        service=lambda context: context.viewer_window_service,
        method=lambda service, request: service.sample_image(request),
    )


class SummarizeViewerWindowRoisCapability(ViewerWindowCapability):
    name = "openhcs_summarize_viewer_window_rois"
    cli_command = "viewer-rois"
    title = "Summarize viewer ROI payload"
    description = (
        "Returns compact ROI counts, bounds, area statistics, and examples "
        "for shape payloads from a running viewer control endpoint, optionally "
        "filtered to one route."
    )
    service = "viewer_window"
    runtime_requirements = ("running_openhcs_viewer_server",)
    data_exposure = (
        "viewer_shape_payloads",
        "viewer_shape_bounds",
        "viewer_roi_statistics",
    )
    input_contract = ViewerWindowRoiSummaryRequest
    output_contract = ViewerWindowRoiSummaryResult
    invocation = AgentViewerWindowRequestServiceInvocation(
        service=lambda context: context.viewer_window_service,
        method=lambda service, request: service.summarize_rois(request),
    )


class ViewerNativePresentationCapability(ViewerWindowCapability):
    """Original derived exposure and shared native-presentation invocation."""

    service = "viewer_window"
    mutating = True
    side_effects = ("mutates_viewer_window_presentation",)
    runtime_requirements = ("running_openhcs_viewer_server",)
    invocation = AgentViewerWindowRequestServiceInvocation(
        service=lambda context: context.viewer_window_service,
        method=lambda service, request: service.presentation(request),
    )


class SetViewerViewportCapability(ViewerNativePresentationCapability):
    name = "openhcs_set_viewer_viewport"
    cli_command = "viewer-viewport"
    title = "Set native viewer viewport"
    description = (
        "Sets finite native 2D camera center (three world coordinates) and positive zoom. "
        "Read native_viewport from viewer state to preserve either member. Returns actual "
        "native readback, without changing pixels, axes, selection or layer transforms. "
        "Unsupported viewer modes fail closed. Settle and snapshot after presentation changes."
    )
    data_exposure = ("viewer_native_viewport",)
    input_contract = ViewerWindowViewportRequest
    output_contract = ViewerWindowViewportResult


class SetViewerImageColorCapability(ViewerNativePresentationCapability):
    name = "openhcs_set_viewer_image_color"
    cli_command = "viewer-image-color"
    title = "Set native image colormap and blending"
    description = (
        "Set an installed Napari colormap and blending mode on one exact mounted scalar "
        "image route. Returns actual native readback. Use colour_mode=LAYER in the "
        "stream's original display_config for simultaneous channel composition, and "
        "the existing image-intensity tool for each route's numeric window. No pixels, "
        "axes, transforms or physical source identities change. RGB images fail closed."
    )
    data_exposure = ("viewer_native_image_color",)
    input_contract = ViewerWindowImageColorRequest
    output_contract = ViewerWindowImageColorResult


class SetViewerNativeWindowCapability(ViewerNativePresentationCapability):
    name = "openhcs_set_viewer_native_window"
    cli_command = "viewer-native-window"
    title = "Read, focus or position the exact detached viewer window"
    description = (
        "Read actual window geometry/focus with presentation={}, or set focus=true "
        "and/or a complete Qt logical client geometry bounded by its current screen. "
        "Addresses only the supplied running viewer endpoint through its native Qt "
        "control action, not the GUI bridge or OS input. Missing endpoints fail without "
        "launch/restart/adoption. Camera, layers, pixel values and axes are unchanged. "
        "Returns native readback; window-manager focus may settle before a later read."
    )
    data_exposure = ("viewer_native_window",)
    input_contract = ViewerWindowNativePresentationRequest
    output_contract = ViewerWindowNativePresentationResult


class SetViewerImageIntensityCapability(ViewerWindowCapability):
    name = "openhcs_set_viewer_image_intensity"
    title = "Set native viewer image intensity"
    description = (
        "Applies complete finite ordered contrast_limits and positive finite gamma "
        "to one mounted native image route, without changing source pixels, "
        "segmentation, transforms, camera, axes or layer selection. Read current "
        "native_intensity from viewer state to preserve either member. Returns "
        "actual native presentation readback, not an echo of the request."
    )
    service = "viewer_window"
    mutating = True
    side_effects = ("mutates_viewer_window_presentation",)
    runtime_requirements = ("running_openhcs_viewer_server",)
    data_exposure = ("viewer_native_image_intensity",)
    input_contract = ViewerWindowImageIntensityRequest
    output_contract = ViewerWindowImageIntensityResult
    invocation = AgentViewerWindowRequestServiceInvocation(
        service=lambda context: context.viewer_window_service,
        method=lambda service, request: service.image_intensity(request),
    )


class NavigateViewerWindowCapability(ViewerWindowCapability):
    name = "openhcs_navigate_viewer_window"
    cli_command = "navigate-viewer"
    title = "Navigate viewer window"
    description = (
        "Sets a viewer layer visible or selected, moves zero-based route-local "
        "axis indices, and can select one zero-based data_index on a native "
        "feature-bearing result layer. display_axes selects an ordered semantic "
        "spatial pair (y/x, z_index/x or z_index/y) for native orthogonal review; "
        "hide planar Shapes before cross-section changes. The returned "
        "native_dimensions reports actual orientation, world position and canvas. "
        "The result reports feature_row_count and "
        "selected_data_indices so agents can verify the visible overlay and "
        "Napari feature-table selection are linked. "
        f"{ViewerNavigationControlOptions.DATA_INDEX_SEMANTICS}."
    )
    service = "viewer_window"
    mutating = True
    side_effects = ("mutates_viewer_window_state",)
    runtime_requirements = ("running_openhcs_viewer_server",)
    data_exposure = (
        "viewer_layer_state",
        "viewer_axis_state",
        "viewer_feature_row_count",
        "viewer_selected_data_indices",
    )
    input_contract = ViewerWindowNavigationRequest
    output_contract = ViewerWindowNavigationResult
    invocation = AgentViewerWindowRequestServiceInvocation(
        service=lambda context: context.viewer_window_service,
        method=lambda service, request: service.navigate_window(request),
    )


class RetireViewerWindowLayersCapability(ViewerNativePresentationCapability):
    name = "openhcs_retire_viewer_window_layers"
    cli_command = "retire-viewer"
    title = "Retire explicit viewer layers"
    description = (
        "After viewer settlement, removes only explicitly selected mounted routes "
        "and releases their native layers and receiver payload caches. Supply "
        "expected_producers as a route-key mapping to each route's complete "
        "producer_identities from viewer state, including invocation_key. The "
        "whole set is checked before removal. Pending intake/display mutations "
        "must reach a known terminal state first; known terminal failed candidates "
        "can be retired. Untargeted routes and persisted source/results remain "
        "intact. Hiding layers is not retirement."
    )
    side_effects = ("retires_explicit_viewer_layers",)
    data_exposure = ("viewer_layer_retirement",)
    input_contract = ViewerWindowLayerRetirementRequest
    output_contract = ViewerWindowLayerRetirementResult


class IsolateViewerWindowLayersCapability(ViewerWindowCapability):
    name = "openhcs_isolate_viewer_window_layers"
    cli_command = "isolate-viewer"
    title = "Isolate viewer layers"
    description = (
        "Shows only selected viewer layers, hides all non-selected viewer "
        "layers, selects one layer, and applies route-local axis indices."
    )
    service = "viewer_window"
    mutating = True
    side_effects = ("mutates_viewer_window_state",)
    runtime_requirements = ("running_openhcs_viewer_server",)
    data_exposure = ("viewer_layer_state", "viewer_axis_state")
    input_contract = ViewerWindowLayerIsolationRequest
    output_contract = ViewerWindowLayerIsolationResult
    invocation = AgentViewerWindowRequestServiceInvocation(
        service=lambda context: context.viewer_window_service,
        method=lambda service, request: service.isolate_layers(request),
    )


class ApplyViewerIntensityWindowCapability(ViewerWindowCapability):
    name = "openhcs_apply_viewer_intensity_window"
    cli_command = "viewer-intensity-window"
    title = "Apply viewer intensity window"
    description = (
        "Computes one finite percentile window over the actual routed image "
        "payload records matching a semantic route coordinate and applies the "
        "resolved absolute limits to the native Napari image layer. Omitted "
        "axis_indices select every real payload coordinate on the route; sparse "
        "display padding is never sampled."
    )
    service = "viewer_window"
    mutating = True
    side_effects = ("mutates_viewer_window_contrast",)
    runtime_requirements = ("running_openhcs_viewer_server",)
    data_exposure = (
        "viewer_payload_identities",
        "viewer_image_intensity_statistics",
    )
    input_contract = ViewerWindowIntensityWindowRequest
    output_contract = ViewerWindowIntensityWindowResult
    invocation = AgentViewerWindowRequestServiceInvocation(
        service=lambda context: context.viewer_window_service,
        method=lambda service, request: service.apply_intensity_window(request),
    )


class ProbeViewerWindowCapability(ViewerWindowCapability):
    name = "openhcs_probe_viewer_window"
    cli_command = "probe-viewer"
    title = "Probe viewer window"
    description = "Quickly reports whether a running OpenHCS viewer control endpoint is reachable."
    service = "viewer_window"
    exposition = ViewerWindowCapability.exposition.refine(
        workflow_stage=CapabilityWorkflowStage.DIAGNOSTIC,
        role=CapabilityRole.DIAGNOSTIC,
    )
    runtime_requirements = ("running_openhcs_viewer_server",)
    data_exposure = ("viewer_identity", "viewer_layer_counts")
    input_contract = ViewerWindowStateRequest
    output_contract = ViewerWindowProbeResult
    invocation = AgentViewerWindowConnectionServiceInvocation(
        service=lambda context: context.viewer_window_service,
        method=lambda service, request: service.probe_window(request),
    )


class ValidateViewerWindowStateCapability(ViewerWindowCapability):
    name = "openhcs_validate_viewer_window_state"
    cli_command = "validate-viewer"
    title = "Validate viewer window state"
    description = (
        "Validates mounted layers, expected axis labels, payload nonzero "
        "metadata, routed coordinate coverage, duplicate/missing payload "
        "coordinates, and payload spatial compatibility for a running "
        "OpenHCS viewer."
    )
    service = "viewer_window"
    runtime_requirements = ("running_openhcs_viewer_server",)
    data_exposure = (
        "viewer_layer_state",
        "viewer_axis_state",
        "viewer_payload_summaries",
        "viewer_coordinate_coverage",
        "viewer_payload_spatial_compatibility",
    )
    input_contract = ViewerWindowValidationRequest
    output_contract = ViewerWindowValidationSummaryResult
    invocation = AgentViewerWindowRequestServiceInvocation(
        service=lambda context: context.viewer_window_service,
        method=lambda service, request: service.validation_summary(request),
    )


class UiListBridgesCapability(UiBridgeCapability):
    name = "openhcs_ui_list_bridges"
    title = "List UI bridges"
    description = (
        "Lists local OpenHCS PyQt UI bridge descriptor summaries visible to this user."
    )
    service = "ui_bridge"
    exposition = UiBridgeCapability.exposition.refine(
        workflow_stage=CapabilityWorkflowStage.DIAGNOSTIC,
        role=CapabilityRole.DIAGNOSTIC,
    )
    data_exposure = ("local_ui_bridge_descriptor_paths",)
    output_contract = UiBridgeCatalog
    invocation = AgentServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service: service.list_bridges(),
    )


class UiBridgeStatusCapability(UiBridgeCapability):
    name = "openhcs_ui_bridge_status"
    cli_command = "ui-status"
    title = "Get UI bridge status"
    description = "Reports whether a local running OpenHCS PyQt UI bridge is reachable."
    service = "ui_bridge"
    exposition = UiBridgeCapability.exposition.refine(
        workflow_stage=CapabilityWorkflowStage.DIAGNOSTIC,
        role=CapabilityRole.DIAGNOSTIC,
    )
    runtime_requirements = ("running_openhcs_ui_bridge",)
    output_contract = UiBridgeStatus
    invocation = AgentConnectionServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, connection: service.status(connection),
    )


class UiListCodeDocumentsCapability(UiCodeDocumentCapability):
    name = "openhcs_ui_list_code_documents"
    cli_command = "code-documents"
    title = "List UI code documents"
    description = (
        "Lists UI code documents with identity.document_id values for follow-up calls."
    )
    service = "ui_bridge"
    runtime_requirements = ("running_openhcs_ui_bridge",)
    security_requirements = ("ui_bridge_auth_token",)
    output_contract = UiCodeDocumentCatalog
    invocation = AgentConnectionServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, connection: service.list_documents(connection),
    )


class UiListStateSurfacesCapability(UiSelectedPlateCapability):
    name = "openhcs_ui_list_state_surfaces"
    cli_command = "state-surfaces"
    title = "List UI state surfaces"
    description = (
        "Lists pollable domain state surfaces, including workflow status and live "
        "measurement results, with identity.surface_id values for follow-up reads."
    )
    service = "ui_bridge"
    exposition = UiSelectedPlateCapability.exposition.refine(
        workflow_stage=CapabilityWorkflowStage.STATUS,
        role=CapabilityRole.PRIMARY,
    )
    runtime_requirements = ("running_openhcs_ui_bridge",)
    security_requirements = ("ui_bridge_auth_token",)
    output_contract = UiStateSurfaceCatalog
    invocation = AgentConnectionServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, connection: service.list_state_surfaces(connection),
    )


class UiGetStateSurfaceCapability(UiSelectedPlateCapability):
    name = "openhcs_ui_get_state_surface"
    cli_command = "state-surface"
    title = "Get UI state surface"
    description = (
        "Reads or polls one typed UI domain state surface such as plate-manager "
        "status rows or bounded live measurement tables."
    )
    service = "ui_bridge"
    exposition = UiSelectedPlateCapability.exposition.refine(
        workflow_stage=CapabilityWorkflowStage.STATUS,
        role=CapabilityRole.PRIMARY,
    )
    runtime_requirements = ("running_openhcs_ui_bridge",)
    data_exposure = ("local_paths",)
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = UiStateSurfaceRequest
    output_contract = UiStateSurfaceDocument
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, request, connection: service.get_state_surface(
            request,
            connection,
        ),
    )


class UiListActionsCapability(UiSemanticActionCapability):
    name = "openhcs_ui_list_actions"
    cli_command = "actions"
    title = "List UI actions"
    description = "Lists invokable UI actions with identity.widget_id/action_id values."
    service = "ui_bridge"
    runtime_requirements = ("running_openhcs_ui_bridge",)
    security_requirements = ("ui_bridge_auth_token",)
    output_contract = UiActionCatalog
    invocation = AgentConnectionServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, connection: service.list_actions(connection),
    )


class UiInvokeActionCapability(UiSemanticActionCapability):
    name = "openhcs_ui_invoke_action"
    cli_command = "invoke-action"
    title = "Invoke UI action"
    description = (
        "Dispatches one running-UI action using the selection_revision_token from "
        f"{UiListActionsCapability.name}; workflow progress is polled through "
        "related state surfaces."
    )
    service = "ui_bridge"
    mutating = True
    side_effects = ("may_mutate_running_ui_state", "may_start_ui_workflow")
    runtime_requirements = ("running_openhcs_ui_bridge",)
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = UiActionInvokeRequest
    output_contract = UiActionInvokeResult
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, request, connection: service.invoke_action(
            request,
            connection,
        ),
    )


class UiSelectedPlateWorkflowCapability(UiSelectedPlateCapability):
    name = "openhcs_ui_selected_plate_workflow"
    cli_command = "selected-workflow"
    title = "Selected plate workflow"
    description = (
        "Dispatches init, compile, or run for the current PlateManager "
        "selection through the UI bridge, preserving user-visible plate rows, "
        "ObjectState snapshots, selected state, and output-plate auto-add."
    )
    service = "ui_bridge"
    exposition = UiSelectedPlateCapability.exposition.refine(
        workflow_stage=CapabilityWorkflowStage.EXECUTION,
        role=CapabilityRole.PRIMARY,
    )
    mutating = True
    side_effects = ("may_mutate_running_ui_state", "may_start_ui_workflow")
    runtime_requirements = ("running_openhcs_ui_bridge",)
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = UiSelectedPlateWorkflowRequest
    output_contract = UiSelectedPlateWorkflowResult
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, request, connection: service.selected_plate_workflow(
            request,
            connection,
        ),
    )


class UiListWindowsCapability(UiWindowCapability):
    name = "openhcs_ui_list_windows"
    cli_command = "windows"
    title = "List UI windows"
    description = "Lists visible/focusable UI windows with identity.window_id values."
    service = "ui_bridge"
    runtime_requirements = ("running_openhcs_ui_bridge",)
    security_requirements = ("ui_bridge_auth_token",)
    output_contract = UiWindowCatalog
    invocation = AgentConnectionServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, connection: service.list_windows(connection),
    )


class UiFocusWindowCapability(UiWindowCapability):
    name = "openhcs_ui_focus_window"
    title = "Focus UI window"
    description = "Focuses one running UI window by stable window id or open ObjectState scope id."
    service = "ui_bridge"
    mutating = True
    side_effects = ("changes_running_ui_focus",)
    runtime_requirements = ("running_openhcs_ui_bridge",)
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = UiWindowFocusRequest
    output_contract = UiWindowFocusResult
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, request, connection: service.focus_window(
            request,
            connection,
        ),
    )


class UiNavigateWindowCapability(UiWindowCapability):
    name = "openhcs_ui_navigate_window"
    title = "Navigate UI window"
    description = (
        "Opens or focuses a UI window, reveals a field, or selects an item in an "
        "embedded manager. For list selection, use the manager's window_id and "
        "the item_id from its current state surface. Using an ObjectState scope "
        "as window_id opens that scope's editor; it does not select a manager row."
    )
    service = "ui_bridge"
    mutating = True
    side_effects = (
        "changes_running_ui_focus",
        "may_open_running_ui_window",
        "may_mutate_running_ui_state",
    )
    runtime_requirements = ("running_openhcs_ui_bridge",)
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = UiWindowNavigateRequest
    output_contract = UiWindowNavigateResult
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, request, connection: service.navigate_window(
            request,
            connection,
        ),
    )


class UiCloseWindowCapability(UiWindowCapability):
    name = "openhcs_ui_close_window"
    title = "Close UI window"
    description = (
        "Requests a normal close for one visible UI bridge window by stable window id."
    )
    service = "ui_bridge"
    mutating = True
    side_effects = ("closes_running_ui_window",)
    runtime_requirements = ("running_openhcs_ui_bridge",)
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = UiWindowCloseRequest
    output_contract = UiWindowCloseResult
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, request, connection: service.close_window(
            request,
            connection,
        ),
    )


class UiSnapshotWindowCapability(UiWindowCapability):
    name = "openhcs_ui_snapshot_window"
    cli_command = "window-snapshot"
    title = "Snapshot UI window"
    description = (
        "Captures a running Qt window to PNG. Immediate capture returns the image; "
        "renderer observations arm an operation_id before a normal UI mutation. "
        "Use operation wait/status to obtain its completed result_payload. "
        "flash_maximum_alpha captures an actual maximum-alpha painted frame; "
        "no_flash requires an inactive baseline and observes target-window starts "
        "and paint frames across the bounded interval."
    )
    service = "ui_bridge"
    mutating = True
    side_effects = ("writes_agent_output_file",)
    runtime_requirements = ("running_openhcs_ui_bridge",)
    data_exposure = ("ui_screenshot", "local_output_path")
    security_requirements = ("ui_bridge_auth_token", "agent_path_policy")
    input_contract = UiWindowSnapshotRequest
    output_contract = UiWindowSnapshotResult
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, request, connection: service.snapshot_window(
            request,
            connection,
        ),
    )


class UiGetWidgetTreeCapability(UiWidgetFallbackCapability):
    name = "openhcs_ui_get_widget_tree"
    cli_command = "widget-tree"
    title = "Get UI widget tree"
    description = (
        "Returns a generic window-manager widget projection for one running "
        "UI window, including visible text, enabled state, clickable "
        "geometry, and action kinds for blind interaction."
    )
    service = "ui_bridge"
    runtime_requirements = ("running_openhcs_ui_bridge",)
    data_exposure = (
        "ui_widget_tree",
        "ui_clickable_geometry",
        "ui_visible_text",
        "ui_widget_enabled_state",
        "ui_action_kinds",
        "object_state_resolved_value_previews",
    )
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = UiWidgetTreeRequest
    output_contract = UiWidgetTreeResult
    invocation = AgentUiWidgetTreeServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, request, connection: service.widget_tree(
            request,
            connection,
        ),
    )


class UiInvokeWidgetActionCapability(UiWidgetFallbackCapability):
    name = "openhcs_ui_invoke_widget_action"
    cli_command = "invoke-widget-action"
    title = "Invoke UI widget action"
    description = (
        "Invokes one generic projected Qt widget action by window id, "
        "widget-tree path id, and action kind."
    )
    service = "ui_bridge"
    mutating = True
    side_effects = ("mutates_running_ui",)
    runtime_requirements = ("running_openhcs_ui_bridge",)
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = UiWidgetActionInvokeRequest
    output_contract = UiWidgetActionInvokeResult
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, request, connection: service.invoke_widget_action(
            request,
            connection,
        ),
    )


class UiListObjectStateScopesCapability(UiObjectStateCapability):
    name = "openhcs_ui_list_object_state_scopes"
    cli_command = "object-state-scopes"
    title = "List ObjectState scopes"
    description = (
        "Lists ObjectState scopes visible to the running OpenHCS UI bridge. "
        "Set scope_visibility.include_system_scopes=true to include global "
        "configuration and root system scopes."
    )
    service = "ui_bridge"
    runtime_requirements = ("running_openhcs_ui_bridge",)
    data_exposure = (
        "object_state_scope_ids",
        "object_type_names",
        "object_state_field_markers",
        "object_state_resolved_value_previews",
    )
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = UiObjectStateScopeListRequest
    output_contract = UiObjectStateScopeCatalog
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, request, connection: service.list_object_state_scopes(
            request,
            connection,
        ),
    )


class UiGetObjectStateFieldsCapability(UiObjectStateCapability):
    name = "openhcs_ui_get_object_state_fields"
    cli_command = "object-state-fields"
    title = "Get ObjectState fields"
    description = (
        "Returns compact ObjectState field rows with raw/resolved previews, "
        "dirty/default markers, inheritance flags, and provenance."
    )
    service = "ui_bridge"
    runtime_requirements = ("running_openhcs_ui_bridge",)
    data_exposure = (
        "object_state_scope_ids",
        "object_state_field_markers",
        "object_state_resolved_value_previews",
        "object_state_field_provenance",
    )
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = UiObjectStateFieldListQuery
    output_contract = UiObjectStateFieldListResult
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, request, connection: service.get_object_state_fields(
            request,
            connection,
        ),
    )


class UiDescribeObjectStateFieldCapability(UiObjectStateCapability):
    name = "openhcs_ui_describe_object_state_field"
    cli_command = "object-state-field-help"
    cli_aliases = ("object-state-help", "field-help")
    title = "Describe ObjectState field"
    description = (
        "Returns Python-introspected docs for one ObjectState field using "
        "its dotted field_path; object_state_scope_id is optional only "
        "when the field path uniquely identifies one live ObjectState field."
    )
    service = "ui_bridge"
    runtime_requirements = ("running_openhcs_ui_bridge",)
    data_exposure = (
        "object_state_scope_ids",
        "object_state_field_paths",
        "docstrings",
        "parameter_descriptions",
        "object_state_resolved_value_previews",
    )
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = UiObjectStateFieldHelpQuery
    output_contract = UiObjectStateFieldHelpResult
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.object_state_field_help_service,
        method=lambda service, request, connection: service.describe_query(
            request,
            connection,
        ),
    )


class UiMutateObjectStateFieldCapability(UiObjectStateCapability):
    name = "openhcs_ui_mutate_object_state_field"
    cli_command = "object-state-set"
    cli_aliases = ("object-state-edit", "object-state-mutate")
    title = "Mutate ObjectState field"
    description = (
        "Applies an unsaved ObjectState field update or reset through the "
        "running UI. Save/commit remains explicit through managed-window "
        "save actions so agents can observe dirty/default feedback first."
    )
    service = "ui_bridge"
    mutating = True
    runtime_requirements = ("running_openhcs_ui_bridge",)
    side_effects = ("mutates_object_state", "records_object_state_snapshot")
    data_exposure = (
        "object_state_scope_ids",
        "object_state_field_paths",
        "object_state_field_markers",
        "object_state_raw_value_previews",
        "object_state_resolved_value_previews",
    )
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = UiObjectStateFieldMutationRequest
    output_contract = UiObjectStateFieldMutationResult
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, request, connection: service.mutate_object_state_field(
            request,
            connection,
        ),
    )


class UiGetCodeDocumentCapability(UiCodeDocumentCapability):
    name = "openhcs_ui_get_code_document"
    cli_command = "code-document"
    cli_aliases = ("get-code-document",)
    title = "Get UI code document"
    description = (
        "Reads a bounded UI-owned code document. clean=True returns sparse "
        "clean source; clean=False returns the full resolved pycodified "
        "object including defaults and inherited values."
    )
    service = "ui_bridge"
    runtime_requirements = ("running_openhcs_ui_bridge",)
    data_exposure = ("local_paths_in_source",)
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = UiCodeDocumentRequest
    output_contract = UiCodeDocument
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, request, connection: service.get_document(
            request,
            connection,
        ),
    )


class UiValidateCodeDocumentCapability(UiCodeDocumentCapability):
    name = "openhcs_ui_validate_code_document"
    cli_command = "validate-code-document"
    title = "Validate UI code document"
    description = "Validates an edited UI code document through the bridge source policy without mutating UI state."
    service = "ui_bridge"
    runtime_requirements = ("running_openhcs_ui_bridge",)
    data_exposure = ("local_paths_in_source",)
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = UiCodeDocumentValidationRequest
    output_contract = UiCodeDocumentValidationResult
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, request, connection: service.validate_document(
            request,
            connection,
        ),
    )


class UiApplyCodeDocumentCapability(UiCodeDocumentCapability):
    name = "openhcs_ui_apply_code_document"
    cli_command = "apply-code-document"
    title = "Apply UI code document"
    description = (
        "Applies an edited UI code document through the running PyQt workflow "
        "with revision protection, returning the resulting ObjectState snapshot, "
        "undo snapshot, and revision tokens."
    )
    service = "ui_bridge"
    mutating = True
    side_effects = ("mutates_running_ui_state",)
    runtime_requirements = ("running_openhcs_ui_bridge",)
    data_exposure = (
        "local_paths_in_source",
        "ui_revision_tokens",
        "object_state_snapshot_refs",
        "object_state_undo_targets",
    )
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = UiCodeDocumentApplyRequest
    output_contract = UiCodeDocumentApplyResult
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, request, connection: service.apply_document(
            request,
            connection,
        ),
    )


class UiListSnapshotsCapability(UiSnapshotCapability):
    name = "openhcs_ui_list_snapshots"
    title = "List UI snapshots"
    description = "Lists ObjectState snapshots visible to the running UI bridge."
    service = "ui_bridge"
    runtime_requirements = ("running_openhcs_ui_bridge",)
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = UiSnapshotListRequest
    output_contract = UiSnapshotCatalog
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, request, connection: service.list_snapshots(
            request,
            connection,
        ),
    )


class UiRestoreSnapshotCapability(UiSnapshotCapability):
    name = "openhcs_ui_restore_snapshot"
    title = "Restore UI snapshot"
    description = (
        "Performs snapshot restoration by returning the running UI to a selected "
        "ObjectState snapshot through the bridge."
    )
    service = "ui_bridge"
    mutating = True
    side_effects = ("mutates_running_ui_state", "time_travels_ui_state")
    runtime_requirements = ("running_openhcs_ui_bridge",)
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = UiSnapshotRestoreRequest
    output_contract = UiSnapshotRestoreResult
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, request, connection: service.restore_snapshot(
            request,
            connection,
        ),
    )


class UiTimeTravelHeadCapability(UiSnapshotCapability):
    name = "openhcs_ui_time_travel_head"
    title = "Return UI to current head"
    description = "Returns the running UI from ObjectState time travel to the current branch head."
    service = "ui_bridge"
    mutating = True
    side_effects = ("mutates_running_ui_state", "time_travels_ui_state")
    runtime_requirements = ("running_openhcs_ui_bridge",)
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = UiTimeTravelHeadRequest
    output_contract = UiSnapshotRestoreResult
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, request, connection: service.time_travel_head(
            request,
            connection,
        ),
    )


class UiListBranchesCapability(UiSnapshotCapability):
    name = "openhcs_ui_list_branches"
    title = "List UI snapshot branches"
    description = "Lists ObjectState branches visible to the running UI bridge."
    service = "ui_bridge"
    runtime_requirements = ("running_openhcs_ui_bridge",)
    security_requirements = ("ui_bridge_auth_token",)
    output_contract = UiBranchCatalog
    invocation = AgentConnectionServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, connection: service.list_branches(connection),
    )


class UiSwitchBranchCapability(UiSnapshotCapability):
    name = "openhcs_ui_switch_branch"
    title = "Switch UI snapshot branch"
    description = (
        "Switches the running UI to another ObjectState branch through the bridge."
    )
    service = "ui_bridge"
    mutating = True
    side_effects = ("mutates_running_ui_state", "time_travels_ui_state")
    runtime_requirements = ("running_openhcs_ui_bridge",)
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = UiBranchSwitchRequest
    output_contract = UiSnapshotRestoreResult
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, request, connection: service.switch_branch(
            request,
            connection,
        ),
    )


class UiGetOperationStatusCapability(UiBridgeCapability):
    name = "openhcs_ui_get_operation_status"
    title = "Get UI bridge operation status"
    description = "Returns status for an active or recent running-UI bridge operation."
    service = "ui_bridge"
    exposition = UiBridgeCapability.exposition.refine(
        workflow_stage=CapabilityWorkflowStage.STATUS,
        role=CapabilityRole.DIAGNOSTIC,
    )
    runtime_requirements = ("running_openhcs_ui_bridge",)
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = OPERATION_ID_INPUT
    output_contract = UiBridgeOperationRef
    invocation = AgentConnectionScalarServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, value, connection: service.get_operation_status(
            value,
            connection,
        ),
    )


class UiWaitForOperationReceiptCapability(UiBridgeCapability):
    name = "openhcs_ui_wait_for_operation_receipt"
    title = "Wait for UI bridge mutation receipt"
    description = (
        "Waits once for a running-UI bridge mutation receipt to reach completed, "
        "failed, or another exact terminal bridge status, preserving outcome, "
        "timestamps, errors, and warnings. This confirms bridge dispatch processing "
        "only; it does not wait for a compile, run, viewer, or other domain workflow "
        "to finish. Read that workflow's authoritative state surface separately."
    )
    service = "ui_bridge"
    exposition = UiBridgeCapability.exposition.refine(
        workflow_stage=CapabilityWorkflowStage.STATUS,
        role=CapabilityRole.PRIMARY,
    )
    runtime_requirements = ("running_openhcs_ui_bridge",)
    security_requirements = ("ui_bridge_auth_token",)
    input_contract = UiBridgeOperationWaitRequest
    output_contract = UiBridgeOperationRef
    invocation = AgentConnectionRequestServiceInvocation(
        service=lambda context: context.ui_bridge_service,
        method=lambda service, request, connection: service.wait_for_operation_receipt(
            request,
            connection,
        ),
    )


def agent_capability_declarations() -> tuple[type[AgentCapabilityDeclaration], ...]:
    _load_capability_extensions()
    return tuple(AgentCapabilityDeclaration.__registry__.values())


_CAPABILITY_EXTENSION_ENTRY_POINT_GROUP = "openhcs.agent.capability_extensions"


@cache
def _load_capability_extensions() -> None:
    """Load optional capability declarations from the package-owned boundary."""
    extensions = tuple(
        extension
        for distribution in distributions()
        for extension in distribution.entry_points
        if extension.group == _CAPABILITY_EXTENSION_ENTRY_POINT_GROUP
    )
    for extension in extensions:
        try:
            extension.load()
        except ModuleNotFoundError as error:
            extension_root = extension.module.partition(".")[0]
            missing_root = (error.name or "").partition(".")[0]
            if missing_root != extension_root:
                raise


def _capability_groups(
    capabilities: tuple[type[AgentCapabilityDeclaration], ...],
) -> tuple[AgentCapabilityGroup, ...]:
    groups: list[AgentCapabilityGroup] = []
    for workflow_group in CapabilityWorkflowGroup:
        grouped_capabilities = tuple(
            capability
            for capability in capabilities
            if capability.exposition.workflow_group is workflow_group
        )
        if not grouped_capabilities:
            continue
        groups.append(
            AgentCapabilityGroup(
                workflow_group=workflow_group,
                capability_names=tuple(
                    capability.name for capability in grouped_capabilities
                ),
                tool_count=sum(
                    1
                    for capability in grouped_capabilities
                    if capability.kind is CapabilityKind.TOOL
                ),
                resource_count=sum(
                    1
                    for capability in grouped_capabilities
                    if capability.kind is CapabilityKind.RESOURCE
                ),
            )
        )
    return tuple(groups)


def _capability_attribute_name(name: str) -> str:
    """Return a Python attribute generated from one final capability ABI name."""
    if name.startswith("openhcs://"):
        name = name.removeprefix("openhcs://")
    elif name.startswith("openhcs_"):
        name = name.removeprefix("openhcs_")
    return name.replace("/", "_").replace("-", "_").replace(":", "_")


agent_capabilities = AgentCapabilityNamespace()


def get_capability_registry(
    capability_transport: CapabilityTransport | None = None,
    capability_surface_profile: LocalCapabilitySurfaceProfile | None = None,
) -> AgentCapabilityRegistry:
    """Return the canonical registry projected through transport and visibility."""
    capabilities = agent_capability_declarations()
    selection = AgentCapabilitySurfaceSelection(
        transport=capability_transport,
        local_profile=(
            FullLocalCapabilitySurfaceProfile()
            if capability_surface_profile is None
            else capability_surface_profile
        ),
    )
    selected_capabilities = tuple(
        capability for capability in capabilities if selection.includes(capability)
    )
    return AgentCapabilityRegistry(
        schema_version=SCHEMA_VERSION,
        capabilities=selected_capabilities,
        groups=_capability_groups(selected_capabilities),
        surface_profile=selection.local_profile.name,
    )


def get_agent_capability(name: str) -> type[AgentCapabilityDeclaration]:
    """Return the declaration that owns one final MCP/resource ABI name."""
    _load_capability_extensions()
    try:
        return AgentCapabilityDeclaration.__registry__[name]
    except KeyError as exc:
        raise KeyError(f"Unknown OpenHCS agent capability: {name}") from exc
