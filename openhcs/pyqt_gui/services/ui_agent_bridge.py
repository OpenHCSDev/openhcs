"""The OpenHCS GUI's in-process UI bridge and its plate-manager code document."""

from __future__ import annotations

import ast
from dataclasses import dataclass, replace
from pathlib import Path
from typing import TYPE_CHECKING

from formbridge.bridge.dto import UiActionInvokeRequest
from formbridge.bridge.in_process import UiAgentBridgeService
from formbridge.bridge.service import serves
from formbridge.contracts import AgentError
from formbridge.services.main_thread_dispatch import MainThreadDispatcher
from pyqt_reactive.services.ui_thread_dispatch import UiThreadDispatcher

from openhcs.agent.dto.common import SCHEMA_VERSION
from openhcs.agent.dto.session import (
    SessionEventBatch,
    SessionEventSummary,
    SessionEventsRequest,
)
from openhcs.agent.dto.ui_bridge import (
    UiSelectedPlateWorkflowRequest,
    UiSelectedPlateWorkflowResult,
)
from openhcs.agent.services.ui_bridge_service import (
    UiBridgeSelectedPlateWorkflowOperation,
    UiBridgeSessionEventsOperation,
)
from openhcs.agent.services.function_catalog_service import (
    FunctionCatalogServiceABC,
    UnknownFunctionIdError,
)
from openhcs.core.function_reference import (
    FunctionReference,
    RegistryFunctionReference,
)
from openhcs.agent.ui_bridge_identities import (
    DatasetListCodeDocumentIdentity,
    DatasetListStateSurfaceIdentity,
    DatasetListWidgetIdentity,
)
from openhcs.ui.shared.plate_manager_code_document import (
    PlateManagerCodeDocumentAuthority,
    PlateManagerCodeNamespace,
    PlateManagerDocumentAssignments,
    PlateManagerOrchestratorCodePayload,
)
from formbridge.bridge.in_process import UiCodeDocumentValidationError

if TYPE_CHECKING:
    from openhcs.authoring.session.session import Session


_ORCHESTRATOR_CODE_DOCUMENT_EXAMPLE = PlateManagerDocumentAssignments(
    plate_paths="['/path/to/plate']",
    global_config="GlobalPipelineConfig(...)",
    per_plate_configs="{'/path/to/plate': PipelineConfig(...)}",
    pipeline_data="{'/path/to/plate': [FunctionStep(...), ...]}",
)


ORCHESTRATOR_CODE_DOCUMENT_PAYLOAD_HINT = (
    "Use the plate-manager orchestrator code document shape: "
    + "; ".join(
        f"{name} = {getattr(_ORCHESTRATOR_CODE_DOCUMENT_EXAMPLE, name)}"
        for name in PlateManagerDocumentAssignments.names()
    )
    + ". "
    f"Read {DatasetListCodeDocumentIdentity.require_value()} "
    "for the current template."
)


@dataclass(frozen=True, slots=True)
class CodeDocumentExecutionResult(PlateManagerOrchestratorCodePayload):
    """Parsed and normalized payload from one declarative UI code document."""

    @classmethod
    def from_payload(
        cls,
        payload: PlateManagerOrchestratorCodePayload,
    ) -> "CodeDocumentExecutionResult":
        return cls(
            plate_paths=payload.plate_paths,
            pipeline_data=payload.pipeline_data,
            global_pipeline_config=payload.global_pipeline_config,
            per_plate_configs=payload.per_plate_configs,
        )

    @property
    def mutation_scope(self) -> str | None:
        if len(self.plate_paths) != 1:
            return None
        return self.plate_paths[0]

    def apply_namespace(self) -> PlateManagerCodeNamespace:
        return PlateManagerCodeDocumentAuthority.to_namespace(self)


class UiCodeDocumentSourcePolicy:
    """Validate that MCP-submitted source is declarative code-mode data."""

    allowed_import_roots = frozenset(("openhcs",))
    allowed_builtin_references = frozenset(("bool", "bytes", "float", "int", "str"))

    def __init__(
        self, function_catalog: FunctionCatalogServiceABC | None = None
    ) -> None:
        self._function_catalog = function_catalog

    def validate(self, source: str) -> tuple[AgentError, ...]:
        try:
            self.prepare(source)
        except UiCodeDocumentValidationError as exc:
            return exc.errors
        return ()

    def prepare(
        self, source: str
    ) -> tuple[ast.Module, DeclarativeCodeDocumentAstValidator]:
        """Validate and retain the exact catalog references admitted by this read."""
        try:
            tree = ast.parse(source)
        except SyntaxError as exc:
            raise UiCodeDocumentValidationError(
                (AgentError.from_exception("invalid_python_source", exc),)
            ) from exc

        visitor = DeclarativeCodeDocumentAstValidator(
            allowed_import_roots=self.allowed_import_roots,
            allowed_external_value_types=(
                PlateManagerCodeDocumentAuthority.declared_external_value_types()
            ),
            allowed_builtin_references=self.allowed_builtin_references,
            function_catalog=self._function_catalog,
        )
        visitor.visit(tree)
        if visitor.errors:
            raise UiCodeDocumentValidationError(tuple(visitor.errors))
        return tree, visitor


class DeclarativeCodeDocumentAstValidator(ast.NodeVisitor):
    """AST validator for the generated plate-manager code document shape."""

    def __init__(
        self,
        *,
        allowed_import_roots: frozenset[str],
        allowed_external_value_types: frozenset[type[object]],
        allowed_builtin_references: frozenset[str],
        function_catalog: FunctionCatalogServiceABC | None = None,
    ) -> None:
        self._allowed_import_roots = allowed_import_roots
        self._allowed_external_value_types = allowed_external_value_types
        self._allowed_builtin_references = allowed_builtin_references
        self._function_catalog = function_catalog
        self.catalog_bindings: dict[tuple[str, str], FunctionReference] = {}
        self.catalog_key_bindings: dict[str, FunctionReference] = {}
        self.registry_lookup_names: set[str] = set()
        self._function_names: set[str] = set()
        self._imported_names: set[str] = set()
        self._path_constructor_names: set[str] = set()
        self._helper_bindings: set[str] = set()
        self._path_bindings: set[str] = set()
        self.errors: list[AgentError] = []

    def visit_Import(self, node: ast.Import) -> None:
        for alias in node.names:
            root_name = alias.name.split(".", maxsplit=1)[0]
            if root_name not in self._allowed_import_roots:
                self._error("unsafe_import", f"Import is not allowed: {alias.name}")
                continue
            self._imported_names.add(alias.asname or root_name)

    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        if node.module is None or node.level:
            self._error("unsafe_import", "Relative imports are not allowed.")
            return
        module_name = node.module
        if module_name == "pathlib":
            for alias in node.names:
                if alias.name != "Path":
                    self._error(
                        "unsafe_import",
                        f"Import is not allowed: pathlib.{alias.name}",
                    )
                    continue
                imported_name = alias.asname or alias.name
                self._imported_names.add(imported_name)
                self._path_constructor_names.add(imported_name)
            return
        root_name = module_name.split(".", maxsplit=1)[0]
        for alias in node.names:
            if alias.name == "*":
                self._error("unsafe_import", "Wildcard imports are not allowed.")
                continue
            lookup = RegistryFunctionReference.registry_lookup
            if (module_name, alias.name) == (lookup.module_name, lookup.function_name):
                self.registry_lookup_names.add(alias.asname or alias.name)
            if (
                root_name not in self._allowed_import_roots
                and not self._is_declared_external_value_import(
                    module_name,
                    alias.name,
                )
                and not self._bind_catalog_import(module_name, alias)
            ):
                self._error(
                    "unsafe_import",
                    f"Import is not allowed: {module_name}.{alias.name}",
                )
                continue
            self._imported_names.add(alias.asname or alias.name)

    def visit_Assign(self, node: ast.Assign) -> None:
        if len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name):
            self._error("unsafe_assignment", "Only one named assignment is allowed.")
            return
        target = node.targets[0]
        if target.id in PlateManagerDocumentAssignments.names():
            self.visit(node.value)
            return
        if target.id in self._helper_bindings:
            self._error(
                "unexpected_assignment",
                f"Unexpected assignment target: {target.id}",
            )
            return
        if self._is_absolute_path_binding(node.value) or self._is_path_expression(
            node.value
        ):
            self._helper_bindings.add(target.id)
            self._path_bindings.add(target.id)
            return
        if self._is_safe_literal_binding(node.value):
            self._helper_bindings.add(target.id)
            return
        self._error(
            "unexpected_assignment",
            f"Unexpected assignment target: {target.id}",
        )

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        self._error("unsafe_assignment", "Annotated assignments are not allowed.")

    def visit_AugAssign(self, node: ast.AugAssign) -> None:
        self._error("unsafe_assignment", "Augmented assignments are not allowed.")

    def visit_Expr(self, node: ast.Expr) -> None:
        self._error("unsafe_statement", "Standalone expressions are not allowed.")

    def visit_Call(self, node: ast.Call) -> None:
        if (
            isinstance(node.func, ast.Name)
            and node.func.id in self.registry_lookup_names
        ):
            self._bind_catalog_key(node)
            return
        if not self._is_approved_constructor_call(node.func):
            self._error("unsafe_call", "Only approved constructor calls are allowed.")
            return
        for arg in node.args:
            self.visit(arg)
        for keyword in node.keywords:
            self.visit(keyword.value)

    def visit_Name(self, node: ast.Name) -> None:
        if not isinstance(node.ctx, ast.Load):
            return
        if (
            node.id in self._imported_names
            or node.id in self._helper_bindings
            or node.id in self._allowed_builtin_references
        ):
            return
        self._error("unknown_name", f"Name is not imported by the document: {node.id}")

    def visit_Attribute(self, node: ast.Attribute) -> None:
        self.visit(node.value)

    def visit_BinOp(self, node: ast.BinOp) -> None:
        if self._is_path_expression(node):
            return
        self._error(
            "unsafe_path_expression",
            "Only validated Path bindings may use the / operator.",
        )

    def visit_List(self, node: ast.List) -> None:
        self._visit_sequence(node.elts)

    visit_Tuple = visit_List
    visit_Set = visit_List

    def visit_Dict(self, node: ast.Dict) -> None:
        for key, value in zip(node.keys, node.values):
            if key is not None:
                self.visit(key)
            self.visit(value)

    def visit_Constant(self, node: ast.Constant) -> None:
        return None

    def generic_visit(self, node: ast.AST) -> None:
        safe_nodes = (
            ast.Module,
            ast.Load,
            ast.keyword,
            ast.UnaryOp,
            ast.USub,
            ast.UAdd,
        )
        if isinstance(node, safe_nodes):
            super().generic_visit(node)
            return
        self._error(
            "unsafe_statement",
            f"Unsupported source construct: {type(node).__name__}",
        )

    def _visit_sequence(self, values: list[ast.expr]) -> None:
        for value in values:
            self.visit(value)

    def _is_approved_constructor_call(self, func: ast.expr) -> bool:
        if isinstance(func, ast.Name):
            return (
                func.id in self._imported_names
                and func.id not in self._function_names
                and func.id[:1].isupper()
            )
        return False

    def _bind_catalog_import(self, module_name: str, alias: ast.alias) -> bool:
        if self._function_catalog is None:
            return False
        identity = (module_name, alias.name)
        if identity not in self.catalog_bindings:
            detail = self._function_catalog.get_by_import_path(
                f"{module_name}.{alias.name}", max_doc_chars=0
            )
            if detail is None:
                return False
            reference = self._function_catalog.reference(detail.entry.function_id)
            if (reference.original_module, reference.function_name) != identity:
                return False
            self.catalog_bindings[identity] = reference
        self._function_names.add(alias.asname or alias.name)
        return True

    def _bind_catalog_key(self, node: ast.Call) -> None:
        """Admit ``get_function('<key>')`` only for a key the catalog owns."""
        match node:
            case ast.Call(args=[ast.Constant(value=str() as key)], keywords=[]):
                pass
            case _:
                self._error(
                    "unsafe_call",
                    "Registry lookups take one literal catalog function id.",
                )
                return
        if self._function_catalog is None:
            self._error("unsafe_call", "Registry lookups need a function catalog.")
            return
        if key in self.catalog_key_bindings:
            return
        try:
            self.catalog_key_bindings[key] = self._function_catalog.reference(key)
        except UnknownFunctionIdError as exc:
            self._error("unknown_function_id", str(exc))

    def _is_absolute_path_binding(self, node: ast.expr) -> bool:
        if not isinstance(node, ast.Call):
            return False
        if not isinstance(node.func, ast.Name):
            return False
        if node.func.id not in self._path_constructor_names:
            return False
        if node.keywords or len(node.args) != 1:
            return False
        value = node.args[0]
        return (
            isinstance(value, ast.Constant)
            and isinstance(value.value, str)
            and Path(value.value).is_absolute()
        )

    @staticmethod
    def _is_safe_literal_binding(node: ast.expr) -> bool:
        """Return whether a helper assignment is one immutable scalar literal."""

        return isinstance(node, ast.Constant) and type(node.value) in (
            str,
            int,
            float,
            bool,
            bytes,
            type(None),
        )

    def _is_path_expression(self, node: ast.expr) -> bool:
        if isinstance(node, ast.Name):
            return node.id in self._path_bindings
        if not isinstance(node, ast.BinOp) or not isinstance(node.op, ast.Div):
            return False
        if not self._is_path_expression(node.left):
            return False
        if not isinstance(node.right, ast.Constant) or not isinstance(
            node.right.value,
            str,
        ):
            return False
        relative = Path(node.right.value)
        return not relative.is_absolute() and ".." not in relative.parts

    def _error(self, code: str, message: str) -> None:
        self.errors.append(AgentError(code=code, message=message))

    def _is_declared_external_value_import(
        self,
        module_name: str,
        imported_name: str,
    ) -> bool:
        return any(
            declared_type.__module__ == module_name
            and declared_type.__name__ == imported_name
            for declared_type in self._allowed_external_value_types
        )


class CatalogFunctionImportProjection(ast.NodeTransformer):
    """Bind approved pipeline imports through their registry compiler contracts."""

    namespace_key = "__openhcs_catalog_references__"

    def __init__(
        self,
        bindings: dict[tuple[str, str], FunctionReference],
        key_bindings: dict[str, FunctionReference],
        lookup_names: set[str],
    ) -> None:
        self.bindings = bindings
        self.key_bindings = key_bindings
        self.lookup_names = lookup_names

    def visit_Call(self, node: ast.Call) -> ast.expr:
        """Bind a validated ``get_function('<key>')`` to the catalog reference."""
        if isinstance(node.func, ast.Name) and node.func.id in self.lookup_names:
            return ast.copy_location(
                ast.Subscript(
                    value=ast.Name(id=self.namespace_key, ctx=ast.Load()),
                    slice=ast.Constant(value=node.args[0].value),
                    ctx=ast.Load(),
                ),
                node,
            )
        return self.generic_visit(node)

    def visit_ImportFrom(self, node: ast.ImportFrom) -> list[ast.stmt]:
        statements: list[ast.stmt] = []
        for alias in node.names:
            identity = (node.module, alias.name)
            if identity in self.bindings:
                statement = ast.Assign(
                    targets=[ast.Name(id=alias.asname or alias.name, ctx=ast.Store())],
                    value=ast.Subscript(
                        value=ast.Name(id=self.namespace_key, ctx=ast.Load()),
                        slice=ast.Tuple(
                            elts=[ast.Constant(value=part) for part in identity],
                            ctx=ast.Load(),
                        ),
                        ctx=ast.Load(),
                    ),
                )
            else:
                statement = ast.ImportFrom(
                    module=node.module, names=[alias], level=node.level
                )
            statements.append(ast.copy_location(statement, node))
        return statements


class UiCodeDocumentExecutionService:
    """Executes validated code-mode source through existing manager hooks."""

    def __init__(self, source_policy: UiCodeDocumentSourcePolicy | None = None) -> None:
        self._source_policy = source_policy or UiCodeDocumentSourcePolicy()

    def validate_source(self, source: str, operations) -> CodeDocumentExecutionResult:
        tree, validation = self._source_policy.prepare(source)
        projection = CatalogFunctionImportProjection(
            validation.catalog_bindings,
            validation.catalog_key_bindings,
            validation.registry_lookup_names,
        )
        executable = compile(
            ast.fix_missing_locations(projection.visit(tree)),
            "<plate-manager-code>",
            "exec",
        )
        namespace = PlateManagerCodeNamespace()
        namespace[projection.namespace_key] = {
            identity: reference.resolve()
            for identity, reference in (
                *projection.bindings.items(),
                *projection.key_bindings.items(),
            )
        }
        exec(executable, namespace)

        try:
            payload = PlateManagerCodeDocumentAuthority.from_namespace(namespace)
        except UiCodeDocumentValidationError:
            raise
        except Exception as exc:
            raise UiCodeDocumentValidationError(
                (
                    AgentError.from_exception(
                        "invalid_orchestrator_code_payload",
                        exc,
                        hint=ORCHESTRATOR_CODE_DOCUMENT_PAYLOAD_HINT,
                    ),
                )
            ) from exc
        return CodeDocumentExecutionResult.from_payload(payload)


class OpenHCSUiAgentBridgeService(UiAgentBridgeService):
    """The OpenHCS GUI's in-process bridge: the generic operations plus its session's."""

    def __init__(
        self,
        *,
        session: "Session | None" = None,
        dispatcher: MainThreadDispatcher | None = None,
        **kwargs,
    ) -> None:
        super().__init__(dispatcher=dispatcher or UiThreadDispatcher(), **kwargs)
        self._session = session

    @serves(UiBridgeSelectedPlateWorkflowOperation)
    def selected_plate_workflow(
        self,
        request: UiSelectedPlateWorkflowRequest,
    ) -> UiSelectedPlateWorkflowResult:
        action_result = self.invoke_action(
            UiActionInvokeRequest(
                widget_id=DatasetListWidgetIdentity.require_value(),
                action_id=request.workflow.value,
                selected_scope_ids=request.selected_scope_ids,
                observed_selection_revision_token=(
                    request.observed_selection_revision_token
                ),
                request_token=request.request_token,
                confirmation_requirement=request.confirmation_requirement,
            )
        )
        if not action_result.workflow_status_surface_ids:
            action_result = replace(
                action_result,
                workflow_status_surface_ids=(
                    DatasetListStateSurfaceIdentity.require_value(),
                ),
            )
        return UiSelectedPlateWorkflowResult(
            schema_version=SCHEMA_VERSION,
            workflow=request.workflow,
            action_result=action_result,
            errors=action_result.errors,
            warnings=action_result.warnings,
        )

    @serves(UiBridgeSessionEventsOperation)
    def session_events(self, request: SessionEventsRequest) -> SessionEventBatch:
        """The hosting session's events; the wait runs off the UI thread."""
        if self._session is None:
            raise LookupError("This UI bridge hosts no session.")
        records = self._session.events_after(
            request.after_sequence, timeout_seconds=request.timeout_seconds
        )
        return SessionEventBatch(
            events=tuple(
                SessionEventSummary(
                    sequence=record.sequence,
                    kind=record.event.kind,
                    scope_id=record.event.scope_id,
                    message=record.event.message,
                )
                for record in records
            ),
            last_sequence=self._session.event_log.last_sequence,
        )

