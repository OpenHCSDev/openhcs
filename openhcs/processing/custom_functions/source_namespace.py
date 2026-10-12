"""Exact execution namespaces owned by custom-function source revisions.

Python's pickle owns the qualified-global protocol. Each source-local helper
keeps its actual type/function identity and is addressed under the source's
canonical callable. The namespace retains the original exec globals, not a
helper registry or a copy of declaration metadata.
"""

from __future__ import annotations

import hashlib
from collections.abc import Callable, Iterator
from dataclasses import dataclass, field
from types import FunctionType
from typing import ClassVar

from openhcs.core.function_contract_metadata import FunctionContractAttribute
from openhcs.processing.custom_functions.validation import ValidationError


@dataclass(frozen=True, slots=True)
class CustomFunctionSource:
    """Content identity of one persisted custom-function declaration."""

    function_name: str
    content_sha256: str

    @staticmethod
    def content_digest(source_bytes: bytes) -> str:
        """The exact byte identity used by preparation, persistence and observers."""
        return hashlib.sha256(source_bytes).hexdigest()


@dataclass(frozen=True, slots=True)
class CustomFunctionSourceRevision:
    """Exact persisted source set owned by ``CustomFunctionManager``."""

    sources: tuple[CustomFunctionSource, ...]

    @property
    def function_names(self) -> frozenset[str]:
        """Return declaration names derived from the manager's file convention."""

        return frozenset(source.function_name for source in self.sources)


@dataclass(frozen=True, slots=True)
class CustomFunctionSourceSnapshot:
    """Exact source bytes with their content proof."""

    source: CustomFunctionSource
    content: bytes

    @property
    def file_name(self) -> str:
        return f"{self.source.function_name}.py"

    @property
    def code(self) -> str:
        """The source text; a source that is not UTF-8 is invalid."""
        try:
            return self.content.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise ValidationError(
                f"Persisted custom function '{self.file_name}' is not UTF-8."
            ) from exc

    def require_declared_name(self, declared_name: str) -> None:
        """A persisted source declares the function its file is named after."""
        if declared_name != self.source.function_name:
            raise ValidationError(
                f"Persisted custom function '{self.file_name}' declares "
                f"'{declared_name}'. The filename and declaration "
                "name must match."
            )


@dataclass(frozen=True, slots=True, eq=False)
class CustomFunctionSourceNamespace:
    """One exact source execution; runtime identity is intentionally nominal."""

    source: CustomFunctionSource
    bindings: dict[str, object] = field(repr=False)
    code: str = field(repr=False)
    """The exact text ``source.content_sha256`` is the hash of."""
    member_prefix: ClassVar[str] = "__openhcs_member_"

    def __post_init__(self) -> None:
        if CustomFunctionSource.content_digest(self.code.encode("utf-8")) != (
            self.source.content_sha256
        ):
            raise ValueError(
                f"Custom function source {self.source.function_name!r}: the text "
                "does not have the declared content hash."
            )

    @classmethod
    def bound_to(cls, declaration: Callable) -> "CustomFunctionSourceNamespace":
        """Return the namespace ``bind`` attached to this declaration."""
        revision = vars(declaration)[FunctionContractAttribute.declaration_revision]
        return vars(declaration)[cls.attribute_of_revision(revision)]

    @staticmethod
    def attribute_of_revision(content_sha256: str) -> str:
        """The attribute of a callable that holds the namespace of one source revision."""
        return f"__openhcs_source_{content_sha256}"

    @property
    def export_attribute(self) -> str:
        """Derive the revision-specific namespace address on its callable."""
        return self.attribute_of_revision(self.source.content_sha256)

    def member_attribute(self, relative_qualname: str) -> str:
        """Encode one lexical name, without colliding with namespace members."""
        return self.member_prefix + relative_qualname.encode("utf-8").hex()

    def bind(self, declaration: Callable) -> None:
        """Qualify existing helpers and attach their sole execution namespace."""
        for relative_qualname, member in tuple(self._owned_members()):
            member.__qualname__ = (
                f"{self.source.function_name}.{self.export_attribute}."
                f"{self.member_attribute(relative_qualname)}"
            )
        vars(declaration)[self.export_attribute] = self
        vars(declaration)[FunctionContractAttribute.declaration_validation] = (
            self.require_current
        )

    def _owned_members(self) -> Iterator[tuple[str, type | FunctionType]]:
        """Discover Python declarations, not imported aliases or runtime locals."""
        module_name = self.bindings["__name__"]
        for name, value in self.bindings.items():
            if name == self.source.function_name:
                continue
            # This discriminates Python's external global-symbol categories,
            # not an OpenHCS role family. Imported types are never renamed.
            if not isinstance(value, (type, FunctionType)):
                continue
            if value.__module__ != module_name or value.__qualname__ != name:
                continue
            yield name, value
            if isinstance(value, type):
                yield from self._nested_classes(value, name)

    def _nested_classes(
        self,
        owner: type,
        relative_qualname: str,
    ) -> Iterator[tuple[str, type]]:
        for name, value in vars(owner).items():
            if not isinstance(value, type):
                continue
            nested_qualname = f"{relative_qualname}.{name}"
            if (
                value.__module__ == self.bindings["__name__"]
                and value.__qualname__ == nested_qualname
            ):
                yield nested_qualname, value
                yield from self._nested_classes(value, nested_qualname)

    def require_current(self) -> None:
        """Reject replaced, removed, changed-on-disk or unpublished ownership."""
        from openhcs.processing.custom_functions.runtime_registry import (
            CustomFunctionRuntimeRegistry,
        )

        with CustomFunctionRuntimeRegistry.lifecycle():
            declaration = CustomFunctionRuntimeRegistry.declaration_for_source(
                self.source
            )
            if declaration is None:
                raise RuntimeError(
                    f"Custom function source {self.source.function_name!r} changed; "
                    "recompile the pipeline."
                )
            declaration.require_source_namespace(self)

    def __getattr__(self, name: str) -> object:
        """Resolve the stdpickle global address through the retained globals."""
        if not name.startswith(self.member_prefix):
            raise AttributeError(name)
        try:
            relative_qualname = bytes.fromhex(name[len(self.member_prefix) :]).decode(
                "utf-8"
            )
        except (ValueError, UnicodeDecodeError) as exc:
            raise AttributeError(name) from exc

        from openhcs.processing.custom_functions.runtime_registry import (
            CustomFunctionRuntimeRegistry,
        )

        with CustomFunctionRuntimeRegistry.lifecycle():
            self.require_current()
            first, *remaining = relative_qualname.split(".")
            try:
                value = self.bindings[first]
            except KeyError as exc:
                raise AttributeError(name) from exc
            for component in remaining:
                value = getattr(value, component)
            return value
