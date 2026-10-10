"""Public JSON descent follows callable declarations, never classification names."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Annotated

import pytest

from openhcs.agent.dto.pipeline import FunctionStepAddRequest
from openhcs.agent.services.pipeline_authoring_service import PipelineAuthoringService
from openhcs.core.callable_contract import CallableContract, callable_request
from openhcs.core.function_patterns import normalize_function_pattern
from openhcs.core.memory.decorators import numpy
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.processing.backends.lib_registry.registry_service import RegistryService
from tests.unit.agent.test_compile_selector_authoring import SelectedDeclarations


class _OffsetCapability:
    def project(self, value):
        return super().project(value) + 3


class _ScaleBehavior:
    def project(self, value):
        return value * 2


class IndependentProjection(_OffsetCapability, _ScaleBehavior, Enum):
    DOUBLE_WITH_OFFSET = "double_with_offset"


@numpy
def independent_declared_projection(
    image,
    *,
    mode: Annotated[IndependentProjection | None, "public projection"] = None,
):
    return image if mode is None else mode.project(image)


@dataclass(frozen=True)
class IndependentProjectionRequest:
    image: object
    mode: IndependentProjection | None = None


@numpy
@callable_request(IndependentProjectionRequest)
def independent_request_projection(request: IndependentProjectionRequest):
    return request.image if request.mode is None else request.mode.project(request.image)


@pytest.fixture(params=(independent_declared_projection, independent_request_projection))
def author(monkeypatch, request):
    function_id, metadata = RegistryService.declared_metadata_for_callable(
        request.param
    )
    monkeypatch.setattr(RegistryService, "_metadata_cache", {function_id: metadata})
    monkeypatch.setattr(RegistryService, "_resolved_reference_callables", {})
    return PipelineAuthoringService(function_catalog=SelectedDeclarations()), function_id


@pytest.mark.parametrize("clean", (False, True))
@pytest.mark.parametrize("mode", ("double_with_offset", "DOUBLE_WITH_OFFSET", None))
def test_new_callable_json_roundtrip_exercises_cooperative_member(author, clean, mode):
    service, function_id = author
    ref = service.create_pipeline()
    service.add_function_step_from_request(FunctionStepAddRequest.from_fields(
        pipeline_id=ref.pipeline_id, function_id=function_id, kwargs={"mode": mode},
    ))
    validation = service.validate(ref)
    assert validation.valid, validation.errors
    document = PipelineDocumentCodec.from_source(service.render_source(ref, clean=clean).source)
    invocation = next(normalize_function_pattern(document.pipeline_steps[0].func).iter_items())
    expected = None if mode is None else IndependentProjection.DOUBLE_WITH_OFFSET
    if mode is None:
        # Clean source legitimately omits a parameter equal to its declared default.
        assert invocation.kwargs_dict in ({}, {"mode": None})
    else:
        assert invocation.kwargs_dict == {"mode": expected}
    contract = invocation.contract
    assert contract.validate_public_kwargs(invocation.kwargs_dict) == tuple(invocation.kwargs_dict.items())
    # Execute both actual hooks through the decoded original enum member's MRO.
    assert contract.resolve_raw_runtime_callable()(5, **invocation.kwargs_dict) == (
        5 if mode is None else 13
    )
    assert IndependentProjection.__mro__.index(_OffsetCapability) < IndependentProjection.__mro__.index(_ScaleBehavior)


@pytest.mark.parametrize("kwargs", (
    {"mode": "not_declared"}, {"mode": True}, {"unknown": "double_with_offset"},
    {"dtype_config": {}}, {"image": 5},
))
def test_public_ingress_rejects_unknown_and_runtime_owned_kwargs(author, kwargs):
    service, function_id = author
    ref = service.create_pipeline()
    service.add_function_step_from_request(FunctionStepAddRequest.from_fields(
        pipeline_id=ref.pipeline_id, function_id=function_id, kwargs=kwargs,
    ))
    assert not service.validate(ref).valid
    with pytest.raises((TypeError, ValueError)):
        service.render_source(ref)


def test_strict_compiler_enum_abi_is_not_a_json_decoder():
    contract = CallableContract.from_callable(independent_declared_projection)
    with pytest.raises(TypeError, match="must match IndependentProjection"):
        contract.validate_public_kwargs({"mode": "double_with_offset"})
