"""Real authoring/decoder/source boundaries, without an execution process."""

from __future__ import annotations

import json
import subprocess
from dataclasses import dataclass, replace
from typing import get_type_hints

import pytest
from pycodify import FormatContext, to_source
from python_introspect import dataclass_from_mapping
from skimage.exposure import adjust_gamma

from openhcs.agent.dto.common import SCHEMA_VERSION
from openhcs.agent.dto.config import ConfigPatch
from openhcs.agent.dto.pipeline import FunctionSpecRef, FunctionStepSpec, PipelineSpec
from openhcs.agent.services.pipeline_authoring_service import PipelineAuthoringService
from openhcs.agent.services.function_catalog_service import FunctionCatalogService
from openhcs.core.function_reference import (
    FunctionReferenceTransportAuthority,
    ImportableFunctionReference,
    RegistryFunctionReference,
)
from openhcs.core.pipeline.funcstep_contract_validator import FuncStepContractValidator
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.core.python_source_literal import PythonSourceLiteral
from openhcs.core.steps.abstract import AbstractStep
from openhcs.mcp.dev_client_core import McpDevToolResult
from openhcs.processing.backends.lib_registry.registry_service import RegistryService
from openhcs.processing.backends.lib_registry.scikit_image_registry import SkimageRegistry
from openhcs.processing.backends.lib_registry.unified_registry import (
    FunctionMetadata,
    ProcessingContract,
)
from openhcs.serialization.json import JsonObject, to_jsonable
import openhcs.serialization.pycodify_formatters  # noqa: F401


@dataclass(frozen=True)
class NewJsonOwner:
    """A new declaration importing only the public alias, not its internals."""

    values: JsonObject


@dataclass(frozen=True)
class ExtendedJsonOwner(NewJsonOwner):
    name: str


class SelectedDeclarationCatalog(FunctionCatalogService):
    """Use the real existing store without user custom-source reconciliation."""

    def _all_metadata(self, **kwargs):
        return RegistryService.cached_metadata_snapshot()


@pytest.fixture(autouse=True)
def no_process_launches(monkeypatch):
    def forbidden(*args, **kwargs):
        pytest.fail("source contract checks must not launch subprocesses")

    monkeypatch.setattr(subprocess, "Popen", forbidden)


def step_receipt():
    return FunctionStepSpec(
        "step-1",
        "paired350_identity",
        (FunctionSpecRef("skimage:exposure.adjust_gamma", {"gamma": 1, "gain": 1}),),
        step_config_overrides={
            "napari_streaming_config": ConfigPatch(
                AbstractStep.config_classes_by_field_name()["napari_streaming_config"].__name__,
                {"enabled": True, "persistent": True, "host": "127.0.0.1",
                 "port": 5992, "transport_mode": "tcp", "channel_mode": "layer"},
            ),
        },
    )


@pytest.mark.parametrize("structured", (True, False))
def test_real_client_decodes_successful_mutation_receipt(structured):
    receipt = PipelineSpec(SCHEMA_VERSION, "pipeline-1", "config-1", (step_receipt(),))
    projected = to_jsonable(receipt)
    wire = {"isError": False, "content": []}
    if structured:
        wire["structuredContent"] = projected
    else:
        wire["content"] = [{"type": "text", "text": json.dumps(projected)}]
    result = McpDevToolResult.from_payload("openhcs_add_function_step", wire)
    assert result.first_decoded_payload() == receipt


def test_recursive_json_alias_keeps_declaration_namespace_in_new_descendant():
    get_type_hints(ExtendedJsonOwner, include_extras=True)
    values = {"nested": [{"zero": 0, "false": False, "absent": None}]}
    restored = dataclass_from_mapping(ExtendedJsonOwner, {"values": values, "name": "new"})
    assert restored == ExtendedJsonOwner(values, "new")


@pytest.fixture
def gamma_metadata(monkeypatch):
    registry = SkimageRegistry()
    wrapped = registry.reconstruct_cached_callable(adjust_gamma, ProcessingContract.FLEXIBLE)
    metadata = FunctionMetadata(
        name="exposure.adjust_gamma", func=wrapped, contract=ProcessingContract.FLEXIBLE,
        registry=registry, module=adjust_gamma.__module__, original_name=adjust_gamma.__name__,
    )
    # Supply one real declaration to the existing catalog, not a fake decoder,
    # serializer, wrapper, or second registry; no global discovery/native launch.
    monkeypatch.setattr(RegistryService, "_metadata_cache", {metadata.composite_key: metadata})
    monkeypatch.setattr(RegistryService, "_resolved_reference_callables", {})
    return metadata


@pytest.mark.parametrize("clean", (True, False))
@pytest.mark.parametrize("kwargs", ({"gamma": 1, "gain": 1}, {"gamma": 0.7, "gain": 1.2}))
def test_real_authoring_render_parse_retains_registry_memory_contract(gamma_metadata, clean, kwargs):
    service = PipelineAuthoringService(function_catalog=SelectedDeclarationCatalog())
    receipt = replace(step_receipt(), functions=(FunctionSpecRef(gamma_metadata.composite_key, kwargs),))
    ref = service.create_pipeline(steps=(receipt,))
    validation = service.validate(ref)
    assert validation.valid, validation.errors
    source = service.render_source(ref, clean=clean).source
    assert "from skimage.exposure.exposure import adjust_gamma" not in source
    restored = PipelineDocumentAuthority.from_source(source)
    step = restored.pipeline_steps[0]
    assert FuncStepContractValidator.validate_function_pattern(step.func, step.name) == ("numpy", "numpy")
    original_step = service.to_function_steps(ref)[0]
    assert FuncStepContractValidator._contracts_from_pattern(step.func, step.name) == (
        FuncStepContractValidator._contracts_from_pattern(original_step.func, original_step.name)
    )
    if kwargs != {"gamma": 1, "gain": 1} or not clean:
        assert step.func[1] == kwargs


def test_registry_reference_formatting_uses_alias_without_resolving(gamma_metadata, monkeypatch):
    reference = FunctionReferenceTransportAuthority.function_reference(gamma_metadata.func)
    monkeypatch.setattr(type(reference), "resolve", lambda self: pytest.fail("formatting resolved a callable"))
    context = FormatContext(name_mappings={("openhcs.processing.func_registry", "get_function"): "lookup"})
    fragment = to_source(reference, context)
    assert fragment.code == "lookup('skimage:exposure.adjust_gamma')"
    assert fragment.imports == frozenset({("openhcs.processing.func_registry", "get_function")})


def test_importable_reference_keeps_original_declaration_import():
    reference = FunctionReferenceTransportAuthority.function_reference(step_receipt)
    assert isinstance(reference, ImportableFunctionReference)
    fragment = to_source(reference, FormatContext())
    assert fragment.code == "step_receipt"
    assert fragment.imports == frozenset({(__name__, "step_receipt")})


def test_original_raw_external_callable_still_fails_memory_contract():
    with pytest.raises(ValueError, match="needs memory type decorator"):
        FuncStepContractValidator.validate_function_pattern(adjust_gamma, "paired350_identity")


def test_decoder_still_rejects_undeclared_dto_fields():
    projected = to_jsonable(step_receipt())
    projected["compatibility_extension"] = True
    with pytest.raises(ValueError, match="undeclared field"):
        dataclass_from_mapping(FunctionStepSpec, projected)


def test_new_reference_family_member_needs_no_generic_formatter_edit(gamma_metadata):
    class NewReference(RegistryFunctionReference):
        def source_expression(self, imported_name):
            return f"({super().source_expression(imported_name)})"

    reference = FunctionReferenceTransportAuthority.function_reference(gamma_metadata.func)
    member = NewReference(import_identity=reference.import_identity, composite_key=reference.composite_key)
    assert to_source(member, FormatContext()).code == "(get_function('skimage:exposure.adjust_gamma'))"


def test_independent_source_capability_composes_through_cooperative_mro(gamma_metadata):
    class ExtraImport(PythonSourceLiteral):
        def source_literal_imports(self):
            return super().source_literal_imports() | frozenset({(__name__, "step_receipt")})

    class ComposedReference(RegistryFunctionReference, ExtraImport):
        pass

    reference = FunctionReferenceTransportAuthority.function_reference(gamma_metadata.func)
    member = ComposedReference(import_identity=reference.import_identity, composite_key=reference.composite_key)
    fragment = to_source(member, FormatContext())
    assert fragment.code == "get_function('skimage:exposure.adjust_gamma')"
    assert fragment.imports == frozenset({
        ("openhcs.processing.func_registry", "get_function"), (__name__, "step_receipt"),
    })


@pytest.mark.parametrize("declaration", (NewJsonOwner, int))
def test_importable_type_formatter_uses_shared_source_literal_owner(declaration):
    fragment = to_source(declaration, FormatContext())
    assert fragment.code == declaration.__name__
    assert fragment.imports == (
        frozenset() if declaration is int else frozenset({(__name__, declaration.__name__)})
    )
