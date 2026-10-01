"""Declaration-only extension through real imports and cooperative class hooks."""

import importlib
import sys
from dataclasses import replace
from types import ModuleType

import pytest

from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.agent.dto.knowledge import KnowledgeBaseDocumentRequest
from openhcs.agent.services.knowledge_base_service import KnowledgeBaseService


@pytest.mark.parametrize("audit_first", [True, False])
@pytest.mark.parametrize("computed_name", [False, True])
def test_independent_declaration_is_selected_with_cooperative_capability(
    tmp_path, monkeypatch, audit_first, computed_name
):
    events = []

    class DeclarationAudit:
        def __init_subclass__(cls, **kwargs):
            events.append(("before", cls.__name__))
            super().__init_subclass__(**kwargs)
            events.append(("after", cls.__name__))

    class AuditBefore(DeclarationAudit, CellProfilerModule):
        pass

    class AuditAfter(CellProfilerModule, DeclarationAudit):
        pass

    root = AuditBefore if audit_first else AuditAfter
    support = ModuleType("selected_declaration_support")
    support.Root = root
    monkeypatch.setitem(sys.modules, support.__name__, support)
    package_name = f"selected_declarations_{audit_first}_{computed_name}"
    package = tmp_path / package_name
    package.mkdir()
    (package / "__init__.py").write_text("")
    (package / "arbitrary_location.py").write_text(
        "from selected_declaration_support import Root\n"
        "class IndependentDeclaration(Root):\n"
        + (f"    module_name = 'IndependentSelection' + str({audit_first})\n"
         if computed_name else f"    module_name = 'IndependentSelection{audit_first}'\n")
        + f"    aliases = ('IndependentAlias{audit_first}',)\n"
        f"    function_name = 'independent_selected_function_{audit_first}'\n"
    )
    (package / "unrelated.py").write_text(
        "raise AssertionError('unrelated module was imported')\n"
    )
    monkeypatch.syspath_prepend(str(tmp_path))
    registry = CellProfilerModule.__registry__
    monkeypatch.setattr(registry, "_discovered", False)
    monkeypatch.setattr(
        registry, "_config", replace(registry._config, discovery_package=package_name)
    )

    def forbid_full_discovery():
        raise AssertionError("selected lookup attempted full discovery")

    monkeypatch.setattr(registry, "_discover", forbid_full_discovery)
    events.clear()
    try:
        declaration = root.require_module(f"INDEPENDENTALIAS{audit_first}".upper())
        assert declaration.__module__ == f"{package_name}.arbitrary_location"
        assert declaration is root.for_module(f"IndependentSelection{audit_first}")
        assert declaration is root.for_backend_function_name(
            f"independent_selected_function_{audit_first}"
        )
        assert events == [
            ("before", "IndependentDeclaration"),
            ("after", "IndependentDeclaration"),
        ]
        assert not registry._discovered
        assert f"{package_name}.unrelated" not in sys.modules
        assert root.for_module("MissingIndependentDeclaration") is None
        with pytest.raises(KeyError):
            root.require_module("MissingIndependentDeclaration")
        (package / "collision.py").write_text(
            "from selected_declaration_support import Root\n"
            "class ConflictingDeclaration(Root):\n"
            f"    module_name = 'IndependentSelection{audit_first}'\n"
            "    aliases = ('ForcedCollisionSelection',)\n"
        )
        importlib.invalidate_caches()
        with pytest.raises(ValueError, match="duplicates CellProfiler module names"):
            root.for_module("ForcedCollisionSelection")
        assert dict.get(registry, f"IndependentSelection{audit_first}") is declaration
    finally:
        dict.pop(registry, f"IndependentSelection{audit_first}", None)
        for name in tuple(sys.modules):
            if name == package_name or name.startswith(f"{package_name}."):
                monkeypatch.delitem(sys.modules, name)
        importlib.invalidate_caches()


def test_examplehuman_selected_source_uses_same_declaration_owner(monkeypatch):
    def forbid_full_discovery():
        raise AssertionError("selected example requested whole-family discovery")

    monkeypatch.setattr(CellProfilerModule.__registry__, "_discover", forbid_full_discovery)
    document = KnowledgeBaseService().get_document(
        KnowledgeBaseDocumentRequest.from_fields(
            document_id="openhcs_official30_benchmark_recipes",
            section_id="examplehuman-openhcs-python",
            max_chars=50000,
        )
    )
    assert not document.errors, document.errors
    assert "pipeline_steps" in document.content
