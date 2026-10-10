import ast
import importlib
import inspect
import pkgutil
import textwrap
from abc import ABC, abstractmethod

import pytest
from metaclass_registry import AutoRegisterMeta

from openhcs.constants.constants import MemoryType
from openhcs.processing.backends.cellprofiler._backend import (
    BackendProvider,
    CellProfilerBackendProvider,
    CellProfilerBackendSelection,
    CellProfilerBackendStrategyMixin,
    DefaultBackendSelection,
    NativeBackendProvider,
    NumbaBackendProvider,
)

DECLARATION_NAMES = frozenset({"memory_type", "backend_provider", "is_default_backend"})


def _backend_families() -> tuple[type[CellProfilerBackendStrategyMixin], ...]:
    import openhcs.processing.backends.cellprofiler as cellprofiler_backends

    for module_info in pkgutil.iter_modules(cellprofiler_backends.__path__):
        importlib.import_module(f"{cellprofiler_backends.__name__}.{module_info.name}")
    importlib.import_module("openhcs.processing.backends.analysis.region_properties")

    def subclasses(cls: type) -> set[type]:
        found = set(cls.__subclasses__())
        for subclass in tuple(found):
            found |= subclasses(subclass)
        return found

    return tuple(
        sorted(
            (
                family
                for family in subclasses(CellProfilerBackendStrategyMixin)
                if "__registry__" in vars(family)
            ),
            key=lambda family: family.__qualname__,
        )
    )


def test_provider_choices_are_derived_from_the_provider_family() -> None:
    providers = {
        name: selection
        for name, selection in CellProfilerBackendSelection.__registry__.items()
        if issubclass(selection, BackendProvider)
    }
    assert {choice.value for choice in CellProfilerBackendProvider} == set(providers)
    for choice in CellProfilerBackendProvider:
        assert choice.provider is providers[choice.value]
    assert CellProfilerBackendProvider.NUMBA.provider is NumbaBackendProvider


def test_selection_inputs_resolve_to_selection_classes() -> None:
    assert CellProfilerBackendSelection.from_input(None) is DefaultBackendSelection
    assert (
        CellProfilerBackendSelection.from_input(CellProfilerBackendProvider.NUMBA)
        is NumbaBackendProvider
    )
    assert (
        CellProfilerBackendSelection.from_input(NumbaBackendProvider)
        is NumbaBackendProvider
    )
    assert DefaultBackendSelection.semantic_identity() == (("selection", "default"),)
    assert NumbaBackendProvider.semantic_identity() == (("selection", "numba"),)
    with pytest.raises(TypeError, match="Backend provider"):
        CellProfilerBackendSelection.from_input("numba")  # type: ignore[arg-type]


def test_every_backend_registers_under_its_declared_memory_type_and_provider() -> None:
    families = _backend_families()
    assert families
    for family in families:
        registry = dict(family.__registry__)
        assert registry, family
        for key, backend in registry.items():
            assert key == backend.backend_provider.backend_key(backend.memory_type)
            assert backend.backend_key == key
            assert (
                family.for_memory_type(
                    backend.memory_type, backend_provider=backend.backend_provider
                ).__class__
                is backend
            )
        memory_types = {backend.memory_type for backend in registry.values()}
        for memory_type in memory_types:
            defaults = [
                backend
                for backend in registry.values()
                if backend.memory_type is memory_type and backend.is_default_backend
            ]
            if defaults:
                assert len(defaults) == 1, (family, defaults)
                assert type(family.for_memory_type(memory_type)) is defaults[0]


def test_every_numba_backend_prepares_its_compiled_kernels() -> None:
    missing = [
        f"{backend.__module__}.{backend.__qualname__}"
        for family in _backend_families()
        for backend in family.__registry__.values()
        if backend.requires_explicit_prepare_backend()
        and backend.prepare_backend is CellProfilerBackendStrategyMixin.prepare_backend
    ]
    assert missing == []


def test_new_backend_needs_only_memory_type_and_provider() -> None:
    class ProbeBackendStrategy(
        CellProfilerBackendStrategyMixin, ABC, metaclass=AutoRegisterMeta
    ):
        @abstractmethod
        def probe(self) -> str: ...

    class NativeProbe(ProbeBackendStrategy):
        memory_type = MemoryType.NUMPY
        backend_provider = NativeBackendProvider
        is_default_backend = True

        def probe(self) -> str:
            return "native"

    class NumbaProbe(NativeProbe):
        backend_provider = NumbaBackendProvider
        is_default_backend = False

        def prepare_backend(self) -> None:
            return

        def probe(self) -> str:
            return "numba"

    assert dict(ProbeBackendStrategy.__registry__) == {
        "numpy:native": NativeProbe,
        "numpy:numba": NumbaProbe,
    }
    assert ProbeBackendStrategy.for_memory_type().probe() == "native"
    assert (
        ProbeBackendStrategy.for_memory_type(
            backend_provider=CellProfilerBackendProvider.NUMBA
        ).probe()
        == "numba"
    )
    assert ProbeBackendStrategy.available_backend_providers(MemoryType.NUMPY) == (
        NativeBackendProvider,
        NumbaBackendProvider,
    )
    with pytest.raises(NotImplementedError, match="opencv"):
        ProbeBackendStrategy.for_memory_type(
            backend_provider=CellProfilerBackendProvider.OPENCV
        )
    with pytest.raises(TypeError, match="both declare"):

        class DuplicateNativeProbe(ProbeBackendStrategy):
            memory_type = MemoryType.NUMPY
            backend_provider = NativeBackendProvider

            def probe(self) -> str:
                return "duplicate"


def _own_body(backend: type) -> str:
    source = textwrap.dedent(inspect.getsource(backend))
    cls = ast.parse(source).body[0]
    body = [
        statement
        for statement in cls.body
        if not (
            isinstance(statement, ast.Assign)
            and all(
                isinstance(target, ast.Name) and target.id in DECLARATION_NAMES
                for target in statement.targets
            )
        )
        and not (
            isinstance(statement, ast.Expr) and isinstance(statement.value, ast.Constant)
        )
    ]
    bases = [ast.dump(base) for base in cls.bases]
    return repr(bases) + "".join(ast.dump(statement) for statement in body)


def test_no_two_backends_in_a_family_are_twins() -> None:
    twins = []
    for family in _backend_families():
        seen: dict[str, type] = {}
        for backend in family.__registry__.values():
            body = _own_body(backend)
            if body in seen:
                twins.append((seen[body].__qualname__, backend.__qualname__))
            seen.setdefault(body, backend)
    assert twins == []
