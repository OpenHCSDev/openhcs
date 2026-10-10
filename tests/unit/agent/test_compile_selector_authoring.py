"""Declaration-owned authoring admission/reconstruction, no native execution."""

from __future__ import annotations

import subprocess

import pytest

from openhcs.agent.dto.pipeline import FunctionSpecRef, FunctionStepSpec
from openhcs.agent.services.function_catalog_service import FunctionCatalogService
from openhcs.agent.services.pipeline_authoring_service import PipelineAuthoringService
from openhcs.core.artifacts import (
    ArtifactSpec,
    ArtifactSpecCollection,
    ImageArtifactType,
)
from openhcs.core.function_patterns import normalize_function_pattern
from openhcs.core.invocation_artifacts import (
    ArtifactDeclarationStepContext,
    InvocationContractPlan,
)
from openhcs.core.memory.decorators import numpy
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.interop.cellprofiler.compile_time_contracts import (
    CellProfilerInvocationContractProviderFactory,
)
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.interop.cellprofiler.module_settings import CellProfilerModuleSettings
from openhcs.interop.cellprofiler.settings_binder import SettingToKeywordBinding
from openhcs.processing.backends.cellprofiler.color import (
    GrayToColorModule,
    gray_to_color,
)
from openhcs.processing.backends.cellprofiler.illumination import (
    CorrectIlluminationApplyModule,
    correct_illumination_apply,
)
from openhcs.processing.backends.cellprofiler.intensity import measure_object_intensity
from openhcs.processing.backends.lib_registry.registry_service import RegistryService


class SelectedDeclarations(FunctionCatalogService):
    def _all_metadata(self, **kwargs):
        return RegistryService.cached_metadata_snapshot()


@numpy
def new_authoring_callable(image, amount=2):
    return image


@pytest.fixture(autouse=True)
def bounded_declarations(monkeypatch):
    def forbidden(*args, **kwargs):
        pytest.fail("source authoring tests must not launch subprocesses")

    monkeypatch.setattr(subprocess.Popen, "__init__", forbidden)
    monkeypatch.setattr(
        RegistryService,
        "_metadata_cache",
        dict(
            RegistryService.declared_metadata_for_callable(func)
            for func in (
                gray_to_color,
                correct_illumination_apply,
                measure_object_intensity,
            )
        ),
    )
    monkeypatch.setattr(RegistryService, "_resolved_reference_callables", {})


def draft(func, kwargs):
    function_id, _metadata = RegistryService.declared_metadata_for_callable(func)
    service = PipelineAuthoringService(function_catalog=SelectedDeclarations())
    ref = service.create_pipeline(
        steps=(
            FunctionStepSpec(
                "step-1", "selector-contract", (FunctionSpecRef(function_id, kwargs),)
            ),
        )
    )
    return service, ref


def selectors():
    red, _green, blue = GrayToColorModule.rgb_channels
    return {
        red.image_binding.require_parameter_name(): "FITC",
        blue.image_binding.require_parameter_name(): "DAPI",
        GrayToColorModule.output_image_binding.require_parameter_name(): "Composite",
    }


def reconstruction(module_type, func, kwargs):
    invocation = next(normalize_function_pattern((func, kwargs)).iter_items())
    # Deliberately reverse source binding order versus declaration role order.
    images = tuple(
        ArtifactSpec.input(name, ImageArtifactType) for name in ("DAPI", "FITC")
    )
    context = ArtifactDeclarationStepContext(
        step_name="selector-contract",
        step_index=0,
        available_artifacts=ArtifactSpecCollection(images),
        main_flow_artifacts=ArtifactSpecCollection(images),
    )
    blocks, consumed = module_type.module_blocks_for_invocation(
        invocation=invocation, step_context=context
    )
    assert blocks, "named selectors must reconstruct without redundant numeric kwargs"
    (numbered,), _next = module_type.number_step_invocation_blocks(
        (blocks,), first_module_num=1
    )
    contract, consumed = module_type.invocation_callable_contract(
        invocation=invocation,
        numbered_module_blocks=numbered,
        consumed_kwarg_names=consumed,
        step_context=context,
    )
    return contract, consumed


@pytest.mark.parametrize("clean", (True, False))
def test_named_selectors_validate_render_parse_and_reconstruct_defaults(clean):
    kwargs = selectors()
    service, ref = draft(gray_to_color, kwargs)
    result = service.validate(ref)
    assert result.valid, result.errors
    restored = PipelineDocumentCodec.from_source(
        service.render_source(ref, clean=clean).source
    )
    invocation = next(
        normalize_function_pattern(restored.pipeline_steps[0].func).iter_items()
    )
    values = invocation.kwargs_dict
    assert values["red_channel"] == 0
    assert values["blue_channel"] == 1
    assert all(values[name] == value for name, value in kwargs.items())
    contract, consumed = reconstruction(GrayToColorModule, gray_to_color, values)
    assert contract.artifact_inputs.names_of_artifact_type(ImageArtifactType) == (
        "FITC",
        "DAPI",
    )
    assert contract.artifact_outputs.names_of_artifact_type(ImageArtifactType) == (
        "Composite",
    )
    assert set(consumed) == set(kwargs)
    executable = dict(
        InvocationContractPlan(
            contract=contract, consumed_kwarg_names=consumed
        ).consume_authored_kwargs(
            invocation,
            ArtifactDeclarationStepContext(step_name="selector-contract", step_index=0),
        )
    )
    assert not set(kwargs).intersection(executable)
    assert executable["red_channel"] == 0
    assert executable["blue_channel"] == 1


def test_original_selector_only_declaration_reconstruction():
    contract, consumed = reconstruction(GrayToColorModule, gray_to_color, selectors())
    assert contract.artifact_inputs.names_of_artifact_type(ImageArtifactType) == (
        "FITC",
        "DAPI",
    )
    assert set(consumed) == set(selectors())


@pytest.mark.parametrize(
    "name", ("image", "runtime_context", "labels", "undeclared_selector")
)
def test_unknown_and_runtime_kwargs_remain_rejected(name):
    service, ref = draft(gray_to_color, {**selectors(), name: "injected"})
    result = service.validate(ref)
    assert not result.valid
    assert result.errors[0].code == "invalid_function_kwargs"
    assert name in result.errors[0].message
    with pytest.raises(ValueError, match="Invalid kwargs"):
        service.render_source(ref)


def test_explicit_callable_choices_are_not_rewritten():
    service, ref = draft(
        gray_to_color, {**selectors(), "red_channel": 1, "blue_channel": 0}
    )
    assert service.validate(ref).valid
    invocation = next(
        normalize_function_pattern(service.to_function_steps(ref)[0].func).iter_items()
    )
    assert invocation.kwargs_dict["red_channel"] == 1
    assert invocation.kwargs_dict["blue_channel"] == 0


def test_output_name_alone_does_not_replace_plain_callable_defaults():
    kwargs = {
        GrayToColorModule.output_image_binding.require_parameter_name(): "Composite"
    }
    service, ref = draft(gray_to_color, kwargs)
    assert service.validate(ref).valid
    invocation = next(
        normalize_function_pattern(service.to_function_steps(ref)[0].func).iter_items()
    )
    assert invocation.kwargs_dict == kwargs


def test_real_runtime_label_parameter_is_not_admitted():
    service, ref = draft(measure_object_intensity, {"labels": "not a runtime payload"})
    result = service.validate(ref)
    assert not result.valid
    assert result.errors[0].code == "invalid_function_kwargs"
    assert "labels" in result.errors[0].message


def test_named_cmyk_defaults_come_from_same_declaration_projection():
    first, _second, _third, last = GrayToColorModule.cmyk_channels
    kwargs = {
        "color_scheme": "CMYK",
        first.image_binding.require_parameter_name(): "FITC",
        last.image_binding.require_parameter_name(): "DAPI",
        GrayToColorModule.output_image_binding.require_parameter_name(): "Composite",
    }
    service, ref = draft(gray_to_color, kwargs)
    assert service.validate(ref).valid
    invocation = next(
        normalize_function_pattern(service.to_function_steps(ref)[0].func).iter_items()
    )
    assert invocation.kwargs_dict[first.channel_parameter] == 0
    assert invocation.kwargs_dict[last.channel_parameter] == 1
    contract, consumed = reconstruction(
        GrayToColorModule, gray_to_color, invocation.kwargs_dict
    )
    assert contract.artifact_inputs.names_of_artifact_type(ImageArtifactType) == (
        "FITC",
        "DAPI",
    )
    assert set(consumed) == set(kwargs) - {"color_scheme"}


def test_additional_real_module_admits_declared_selectors():
    kwargs = {
        binding.require_parameter_name(): f"Chosen{position}"
        for position, binding in enumerate(
            CorrectIlluminationApplyModule.declared_artifact_bindings()
        )
    }
    service, ref = draft(correct_illumination_apply, kwargs)
    assert service.validate(ref).valid
    restored = PipelineDocumentCodec.from_source(service.render_source(ref).source)
    invocation = next(
        normalize_function_pattern(restored.pipeline_steps[0].func).iter_items()
    )
    assert invocation.kwargs_dict == kwargs


def test_new_declaration_composes_independent_settings_without_consumer_edits(
    monkeypatch,
):
    class ExtraOutputSettings(CellProfilerModuleSettings):
        setting_bindings = (
            SettingToKeywordBinding.output("Name the extra image", ImageArtifactType),
        )

        @classmethod
        def authoring_default_kwargs(cls, module, *, authored_kwargs):
            return {
                **super().authoring_default_kwargs(
                    module, authored_kwargs=authored_kwargs
                ),
                "amount": 3,
            }

    class NewAuthoringModule(CellProfilerModule, ExtraOutputSettings):
        module_name = "AuthoringNewDeclaration360"
        function_name = "new_authoring_callable"
        setting_bindings = (
            SettingToKeywordBinding.input("Choose new image", ImageArtifactType),
        )

    try:
        assert NewAuthoringModule.__mro__.index(
            ExtraOutputSettings
        ) < NewAuthoringModule.__mro__.index(CellProfilerModuleSettings)
        key, metadata = RegistryService.declared_metadata_for_callable(
            new_authoring_callable
        )
        monkeypatch.setitem(RegistryService._metadata_cache, key, metadata)
        kwargs = {
            binding.require_parameter_name(): f"New{position}"
            for position, binding in enumerate(
                NewAuthoringModule.declared_artifact_bindings()
            )
        }
        assert len(kwargs) == 2
        service, ref = draft(new_authoring_callable, kwargs)
        assert service.validate(ref).valid
        restored = PipelineDocumentCodec.from_source(
            service.render_source(ref).source
        )
        invocation = next(
            normalize_function_pattern(restored.pipeline_steps[0].func).iter_items()
        )
        assert invocation.kwargs_dict == {**kwargs, "amount": 3}
    finally:
        dict.__delitem__(
            CellProfilerModule.__registry__, NewAuthoringModule.module_name
        )


def test_duplicate_provider_authoring_claims_fail_closed():
    class DuplicateOwner(CellProfilerInvocationContractProviderFactory):
        pass

    try:
        service, ref = draft(gray_to_color, selectors())
        result = service.validate(ref)
        assert not result.valid
        assert (
            "Multiple invocation contract providers claimed authoring kwargs"
            in result.errors[0].message
        )
    finally:
        dict.__delitem__(DuplicateOwner.__registry__, DuplicateOwner.__name__)
