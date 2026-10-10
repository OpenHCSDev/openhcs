"""Session operations: one declaration per thing a client can ask the session to do.

Each operation is a :class:`SessionOperation` subclass. The same class is a
GUI button (label, tooltip), a UI-bridge action (``operation_id``) and, unless
it only presents something, an MCP tool derived from it in
``openhcs.agent.capabilities``. Operations ask the session for everything;
they keep no state.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING, ClassVar

from metaclass_registry import AutoRegisterMeta, LazyDiscoveryDict, RegistryConfig

from openhcs.agent.dto.common import AgentError, AgentWarning
from openhcs.agent.dto.session import NoArgumentsRequest, SessionOperationResult

if TYPE_CHECKING:
    from openhcs.authoring.session.session import Session

_SESSION_OPERATIONS = LazyDiscoveryDict(enable_cache=False)


class SessionOperation(
    ABC,
    metaclass=AutoRegisterMeta,
    registry_config=RegistryConfig(
        registry_dict=_SESSION_OPERATIONS,
        key_attribute="operation_id",
        skip_if_no_key=True,
        registry_name="session operation",
        discovery_package=__name__,
    ),
):
    """One thing a client can ask the session to do."""

    __registry__ = _SESSION_OPERATIONS
    __registry_key__ = "operation_id"
    __skip_if_no_key__ = True

    operation_id: ClassVar[str | None] = None
    """Boundary id: the UI-bridge action id and the MCP tool's suffix."""
    label: ClassVar[str]
    tooltip: ClassVar[str]
    description: ClassVar[str]
    request: ClassVar[type] = NoArgumentsRequest
    result: ClassVar[type] = SessionOperationResult
    side_effects: ClassVar[tuple[str, ...]] = ()
    warnings: ClassVar[tuple[AgentWarning, ...]] = ()
    """Caveats every result of this operation carries."""
    confirmation_required: ClassVar[bool] = True
    selection_mode: ClassVar[str] = "selected"
    """How a renderer fills ``scope_ids``: from the "selected" or "current" rows."""

    @classmethod
    def all(cls) -> tuple[type["SessionOperation"], ...]:
        return tuple(cls.__registry__.values())

    @classmethod
    def named(cls, operation_id: str) -> type["SessionOperation"]:
        try:
            return cls.__registry__[operation_id]
        except KeyError:
            raise ValueError(f"Unknown session operation: {operation_id!r}") from None

    @classmethod
    def resolved(cls, session: "Session") -> type["SessionOperation"]:
        """The operation a button bound to this one runs now (default: itself)."""

        del session
        return cls

    @classmethod
    def button_label(cls, session: "Session") -> str:
        del session
        return cls.label

    @classmethod
    def available(cls, session: "Session", request: object) -> AgentError | None:
        """Why the operation cannot run now, or ``None`` when it can."""

        del session, request
        return None

    @classmethod
    def request_for_selection(
        cls,
        session: "Session",
        scope_ids: tuple[str, ...],
    ) -> object:
        """The request a renderer sends for the given row selection."""

        del session, scope_ids
        return cls.request()

    @classmethod
    @abstractmethod
    def run(cls, session: "Session", request: object) -> SessionOperationResult: ...

    @classmethod
    def invoke(cls, session: "Session", request: object) -> SessionOperationResult:
        """Check availability, then run."""

        error = cls.available(session, request)
        if error is not None:
            return cls.rejected(session, error)
        try:
            return cls.run(session, request)
        except Exception as exc:
            return cls.rejected(
                session, AgentError.from_exception(f"{cls.operation_id}_failed", exc)
            )

    @classmethod
    def completed(
        cls,
        session: "Session",
        scope_ids: tuple[str, ...] = (),
    ) -> SessionOperationResult:
        return SessionOperationResult(
            operation_id=cls.operation_id or cls.__name__,
            status="completed",
            target_scope_ids=scope_ids,
            event_sequence=session.event_log.last_sequence,
            warnings=cls.warnings,
        )

    @classmethod
    def accepted(
        cls,
        session: "Session",
        scope_ids: tuple[str, ...] = (),
    ) -> SessionOperationResult:
        """Work continues in the background; follow the session's events."""

        return SessionOperationResult(
            operation_id=cls.operation_id or cls.__name__,
            status="accepted",
            target_scope_ids=scope_ids,
            event_sequence=session.event_log.last_sequence,
            warnings=cls.warnings,
        )

    @classmethod
    def rejected(cls, session: "Session", error: AgentError) -> SessionOperationResult:
        return SessionOperationResult(
            operation_id=cls.operation_id or cls.__name__,
            status="rejected",
            event_sequence=session.event_log.last_sequence,
            errors=(error,),
        )


class HeadlessOperation(SessionOperation):
    """An operation any session runs, so MCP exposes it as a tool."""


class RendererOperation(SessionOperation):
    """An operation that asks the attached renderer to present something."""

    confirmation_required = False

    @classmethod
    def available(cls, session: "Session", request: object) -> AgentError | None:
        error = super().available(session, request)
        if error is not None:
            return error
        if not session.renderer.presents(cls):
            return AgentError(
                code="renderer_required",
                message=f"{cls.label} needs a renderer; this session has none.",
            )
        return session.renderer.unavailable_reason(cls, request)

    @classmethod
    def run(cls, session: "Session", request: object) -> SessionOperationResult:
        session.renderer.present(cls, request)
        return cls.completed(session)
