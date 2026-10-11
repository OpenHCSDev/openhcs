import pickle
import sys
from dataclasses import field, make_dataclass
from enum import Enum
from inspect import Parameter, signature
from types import MappingProxyType, ModuleType

import pytest
from arraybridge import MemoryContractAttribute, SliceBySliceRuntimeParameter
from metaclass_registry import AutoRegisterMeta
from python_introspect import parameter_exclusions

from openhcs.core.autoregister_preparation import AutoRegisterRegistryPreparation
from openhcs.core.callable_contract import (
    CallableContract,
    CallableImportIdentity,
    CallableMetadata,
    CallableMetadataReader,
    CompilerPreparedAutoRegisterFamily,
    PayloadAxisRequirement,
    PayloadAxisTransition,
    PreservedPayloadAxes,
    attach_callable_contract_metadata,
    prepare_module_autoregister_families,
    prepare_processing_callable,
    preserves_payload_axes,
    requires_payload_axis,
    reset_processing_callable_preparation_cache,
    runtime_image_execution_mode,
)
from openhcs.core.config import LazyDtypeConfig
import openhcs.core.config as config_module
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.function_contract_metadata import FunctionContractAttribute
from openhcs.core.function_reference import (
    FunctionReferenceTransportAuthority,
    ImportableFunctionReference,
    RegistryFunctionReference,
)
from openhcs.core.function_patterns import normalize_function_pattern
from openhcs.core.memory.decorators import numpy
from openhcs.core.pipeline.artifact_planning import extract_artifact_declarations
from openhcs.core.pipeline.function_contracts import (
    required_axis_roles,
    runtime_bound_parameters,
    special_inputs,
)
from openhcs.core.runtime_batch_contracts import (
    RuntimeBatchExecutionDomain,
    RuntimePure2DSliceBatchRequest,
    SliceIndexRuntimeParameter,
    measurement_image_batch_executor,
    pure_2d_batch_executor,
)
from openhcs.processing.backends.lib_registry.cupy_registry import CupyRegistry
from openhcs.core.processing_contracts import (
    FlexibleContract,
    Pure2DContract,
    Pure3DContract,
)
from openhcs.core.axes import ColourAxis, TimeAxis
from openhcs.domains.microscopy.axes import Microscopy
from openhcs.core.image_payload_execution_mode import (
    FullStackExecution,
)

_AUTOREGISTER_PREPARED_TEST_FAMILY_CALLS = 0


def test_external_registry_adapter_declares_execution_memory() -> None:
    """External adapters execute in the same framework they declare at boundaries."""

    def external_filter(image):
        return image

    registry = object.__new__(CupyRegistry)
    adapter = registry.create_library_adapter(
        external_filter,
        FlexibleContract,
    )

    contract = CallableContract.from_callable(adapter)
    assert contract.input_memory_type == "cupy"
    assert contract.output_memory_type == "cupy"
    assert contract.execution_memory_type == "cupy"


class _PreparedAutoRegisterFamily(
    CompilerPreparedAutoRegisterFamily,
    metaclass=AutoRegisterMeta,
):
    __registry_key__ = "registry_key"
    __skip_if_no_key__ = True
    registry_key = None

    @classmethod
    def prepare_registered_family(cls) -> None:
        global _AUTOREGISTER_PREPARED_TEST_FAMILY_CALLS
        _AUTOREGISTER_PREPARED_TEST_FAMILY_CALLS += 1


class _PreparedAutoRegisterImplementation(_PreparedAutoRegisterFamily):
    registry_key = "prepared"


def _function_with_imported_prepared_family(image):
    return image


def _batch_executor(request):
    return request


def _measurement_batch_executor(func, requests, execute_request):
    return [execute_request(func, request) for request in requests]


def _override_batch_executor(request):
    return request


@measurement_image_batch_executor(_measurement_batch_executor)
@pure_2d_batch_executor(_batch_executor)
def _function_with_runtime_batch_executor(image):
    return image


@pure_2d_batch_executor(_override_batch_executor)
def _function_with_batch_override(image):
    return image


def test_callable_contract_reads_runtime_image_execution_mode() -> None:
    @runtime_image_execution_mode(FullStackExecution)
    def process(image):
        return image

    contract = CallableContract.from_callable(process)

    assert contract.runtime_image_execution_mode is FullStackExecution


def test_callable_contract_preserves_payload_axis_requirement() -> None:
    @requires_payload_axis(ColourAxis)
    def process(image):
        return image

    contract = CallableContract.from_callable(process)

    assert (
        contract.payload_axis_requirement
        == PayloadAxisRequirement(ColourAxis)
    )
    assert (
        contract.metadata.as_namespace()[
            FunctionContractAttribute.payload_axis_requirement
        ]
        == PayloadAxisRequirement(ColourAxis)
    )


def test_callable_metadata_rejects_string_payload_axis_requirement() -> None:
    with pytest.raises(TypeError, match="PayloadAxisRequirement"):
        CallableMetadata(payload_axis_requirement="source_channel_axis")


def test_callable_metadata_reader_rejects_wrong_requirement_kind() -> None:
    def process(image):
        return image

    process.__dict__[FunctionContractAttribute.payload_axis_requirement] = (
        PreservedPayloadAxes()
    )

    with pytest.raises(TypeError, match="PayloadAxisRequirement"):
        CallableContract.from_callable(process)


def test_callable_metadata_reader_returns_declared_requirement_kinds() -> None:
    reader = CallableMetadataReader(
        {
            FunctionContractAttribute.payload_axis_requirement: (
                PayloadAxisRequirement(ColourAxis)
            ),
            FunctionContractAttribute.payload_axis_transition: (
                PreservedPayloadAxes()
            ),
        },
        "process",
    )

    requirement = reader.optional_instance(
        FunctionContractAttribute.payload_axis_requirement,
        PayloadAxisRequirement,
    )
    transition = reader.optional_instance(
        FunctionContractAttribute.payload_axis_transition,
        PayloadAxisTransition,
    )

    assert requirement == PayloadAxisRequirement(ColourAxis)
    assert transition == PreservedPayloadAxes()


def test_callable_contract_preserves_declared_payload_axis_transition() -> None:
    @preserves_payload_axes
    def crop_like(image):
        return image

    contract = CallableContract.from_callable(crop_like)

    assert (
        contract.payload_axis_transition
        == PreservedPayloadAxes()
    )
    assert (
        contract.metadata.as_namespace()[
            FunctionContractAttribute.payload_axis_transition
        ]
        == PreservedPayloadAxes()
    )


def test_callable_contract_exposes_canonical_raw_import_identity() -> None:
    def process(image):
        return image

    contract = CallableContract.from_callable(process)

    assert contract.canonical_raw_import_identity() == CallableImportIdentity(
        module_name=__name__,
        function_name="process",
    )
    assert contract.canonical_raw_import_identity().import_path == f"{__name__}.process"


def test_callable_contract_reads_runtime_bound_parameters() -> None:
    @runtime_bound_parameters(SliceIndexRuntimeParameter)
    def process(image, *, slice_index: int = 0):
        del slice_index
        return image

    contract = CallableContract.from_callable(process)

    assert contract.runtime_bound_parameters == ("slice_index",)
    assert contract.runtime_bound_parameter_types == (SliceIndexRuntimeParameter,)
    assert CallableMetadata.from_callable(process).as_namespace()[
        FunctionContractAttribute.runtime_bound_parameters
    ] == (SliceIndexRuntimeParameter,)


def test_callable_contract_validates_nominal_enum_values_from_resolved_annotations() -> (
    None
):
    class ProjectionMethod(Enum):
        MAX = "max"

    def project(image, method: ProjectionMethod = ProjectionMethod.MAX):
        return image

    contract = CallableContract.from_callable(project)

    assert contract.validate_public_kwargs({"method": ProjectionMethod.MAX}) == (
        ("method", ProjectionMethod.MAX),
    )
    with pytest.raises(TypeError, match="project.method must be ProjectionMethod"):
        contract.validate_public_kwargs({"method": "max"})

    assert contract.decode_public_kwargs({"method": "max"}) == {"method": ProjectionMethod.MAX}
    assert contract.decode_public_kwargs({"method": "MAX"}) == {"method": ProjectionMethod.MAX}
    assert contract.decode_public_kwargs({"method": ProjectionMethod.MAX}) == {"method": ProjectionMethod.MAX}
    with pytest.raises(TypeError, match="project.method must be ProjectionMethod"):
        contract.decode_public_kwargs({"method": None})
    with pytest.raises(ValueError, match="not a valid"):
        contract.decode_public_kwargs({"method": "missing"})


@pytest.mark.parametrize("slice_by_slice", [False, True])
def test_callable_contract_preserves_declared_semantic_controls(slice_by_slice) -> None:
    @runtime_bound_parameters(SliceBySliceRuntimeParameter)
    def process(image, *, slice_by_slice: bool = False):
        return image

    contract = CallableContract.from_callable(process)
    assert contract.validate_public_kwargs({"slice_by_slice": slice_by_slice}) == (
        ("slice_by_slice", slice_by_slice),
    )
    assert contract.validate_public_kwargs({}) == ()


def test_callable_contract_still_rejects_injected_runtime_values() -> None:
    @runtime_bound_parameters(SliceIndexRuntimeParameter)
    def process(image, *, slice_index: int = 0):
        return image

    contract = CallableContract.from_callable(process)
    with pytest.raises(TypeError, match="runtime-owned parameter 'slice_index'"):
        contract.validate_public_kwargs({"slice_index": 3})


def test_callable_contract_reads_wrapper_declared_config_parameters(monkeypatch) -> None:
    @numpy(contract=Pure3DContract)
    def process(image):
        return image

    contract = CallableContract.from_callable(process)
    declared_parameter = contract.canonical_signature.parameters["dtype_config"]
    assert isinstance(signature(process).parameters["dtype_config"].default, LazyDtypeConfig)

    def forbidden_config_value(*args, **kwargs):
        raise AssertionError("Config schema discovery constructed a value")

    monkeypatch.setattr(LazyDtypeConfig, "__init__", forbidden_config_value)

    assert contract.config_bound_parameter_names == ("dtype_config",)
    assert contract.runtime_owned_parameter_names == frozenset({"dtype_config"})
    assert contract.overridable_runtime_parameter_names == frozenset({"dtype_config"})
    assert contract.validate_public_kwargs({}) == ()
    (parameter,) = contract.config_bound_parameters
    assert parameter.annotation is LazyDtypeConfig
    assert parameter.default is declared_parameter.default

    graph = extract_artifact_declarations(process)
    parameters = graph.config_parameters_for_step("process")
    assert tuple(parameter.name for parameter in parameters) == ("dtype_config",)

    def forbidden_signature_read(owner):
        raise AssertionError("Axis binding repeated admitted config schema discovery")

    monkeypatch.setattr(
        CallableContract, "config_bound_parameters", property(forbidden_signature_read)
    )
    assert graph.config_parameters_for_step("process") is parameters


def test_config_parameter_schema_refreshes_from_replaced_pipeline_declaration(monkeypatch):
    def forbidden_default():
        raise AssertionError("Config field discovery evaluated a default factory")

    original_default = object()
    parameter = Parameter(
        "custom_config", Parameter.KEYWORD_ONLY,
        annotation=LazyDtypeConfig, default=original_default,
    )
    for declared_type, admitted in ((LazyDtypeConfig, True), (int, False)):
        replacement = make_dataclass(
            "PipelineConfig",
            [("custom_config", declared_type, field(default_factory=forbidden_default))],
        )
        monkeypatch.setattr(config_module, "PipelineConfig", replacement)
        resolved = config_module.runtime_config_parameter(parameter)
        if admitted:
            assert resolved is parameter
            assert resolved.default is original_default
        else:
            assert resolved is None


def test_callable_contract_preserves_arraybridge_execution_declaration() -> None:
    @numpy(contract=Pure2DContract)
    def process(image):
        return image

    contract = CallableContract.from_callable(process)
    namespace = contract.metadata.as_namespace()

    assert contract.input_memory_type == "numpy"
    assert contract.output_memory_type == "numpy"
    assert contract.execution_memory_type == "numpy"
    assert namespace[MemoryContractAttribute.EXECUTION.value] == "numpy"


def test_memory_wrapper_preserves_declared_parameter_exclusions() -> None:
    @numpy(contract=Pure2DContract)
    @special_inputs("mask")
    def process(image, *, mask):
        return image

    assert "mask" in parameter_exclusions(process)


def test_callable_contract_projects_runtime_context_exclusion() -> None:
    """Generic forms derive hidden runtime context from the callable contract."""

    @numpy(contract=Pure2DContract)
    def process(image, *, context: ProcessingContext):
        del context
        return image

    assert "context" in parameter_exclusions(process)
    assert CallableContract.from_callable(process).runtime_owned_parameter_names == (
        frozenset({"context", "dtype_config"})
    )


def test_callable_contract_reads_required_axis_roles() -> None:
    @required_axis_roles(TimeAxis)
    def process(image):
        return image

    contract = CallableContract.from_callable(process)

    assert contract.required_axis_roles == (TimeAxis,)
    assert CallableMetadata.from_callable(process).as_namespace()[
        FunctionContractAttribute.required_axis_roles
    ] == (TimeAxis,)


def test_callable_contract_reads_runtime_image_execution_mode_from_function_reference() -> (
    None
):
    reference = ImportableFunctionReference(
        import_identity=CallableImportIdentity(
            module_name=__name__,
            function_name="_function_with_runtime_batch_executor",
        ),
        composite_key=f"{__name__}:_function_with_runtime_batch_executor",
        metadata=CallableMetadata(
            runtime_image_execution_mode=FullStackExecution,
        ),
    )

    contract = CallableContract.from_callable(reference)

    assert contract.runtime_image_execution_mode is FullStackExecution


def test_callable_contract_metadata_preserves_explicit_nominal_processing_contract() -> (
    None
):
    def process(image):
        return image

    vars(process)[
        FunctionContractAttribute.processing_contract
    ] = FlexibleContract

    attach_callable_contract_metadata(process, processing_contract=Pure2DContract)

    contract = CallableContract.from_callable(process)
    assert (
        vars(process)[FunctionContractAttribute.processing_contract]
        is FlexibleContract
    )
    assert contract.processing_contract is FlexibleContract


def test_prepare_processing_callable_warms_imported_registered_families() -> None:
    global _AUTOREGISTER_PREPARED_TEST_FAMILY_CALLS
    _AUTOREGISTER_PREPARED_TEST_FAMILY_CALLS = 0
    reset_processing_callable_preparation_cache()

    prepare_processing_callable(_function_with_imported_prepared_family)

    assert _AUTOREGISTER_PREPARED_TEST_FAMILY_CALLS == 1


def test_prepare_processing_callable_does_not_warm_unrelated_loaded_families() -> None:
    calls = {"related": 0, "unrelated": 0}

    class RelatedFamily(CompilerPreparedAutoRegisterFamily, metaclass=AutoRegisterMeta):
        __registry_key__ = "registry_key"
        __skip_if_no_key__ = True
        registry_key = None

        @classmethod
        def prepare_registered_family(cls) -> None:
            calls["related"] += 1

    class RelatedImplementation(RelatedFamily):
        registry_key = "related"

    class UnrelatedFamily(
        CompilerPreparedAutoRegisterFamily,
        metaclass=AutoRegisterMeta,
    ):
        __registry_key__ = "registry_key"
        __skip_if_no_key__ = True
        registry_key = None

        @classmethod
        def prepare_registered_family(cls) -> None:
            calls["unrelated"] += 1

    class UnrelatedImplementation(UnrelatedFamily):
        registry_key = "unrelated"

    def process(image):
        return image

    related_module = ModuleType("tests.unit._warmup_related_module")
    unrelated_module = ModuleType("tests.unit._warmup_unrelated_module")
    related_module.RelatedFamily = RelatedFamily
    related_module.RelatedImplementation = RelatedImplementation
    related_module.process = process
    unrelated_module.UnrelatedFamily = UnrelatedFamily
    unrelated_module.UnrelatedImplementation = UnrelatedImplementation
    process.__module__ = related_module.__name__

    reset_processing_callable_preparation_cache()
    sys.modules[related_module.__name__] = related_module
    sys.modules[unrelated_module.__name__] = unrelated_module
    try:
        prepare_processing_callable(process)
    finally:
        sys.modules.pop(related_module.__name__, None)
        sys.modules.pop(unrelated_module.__name__, None)
        reset_processing_callable_preparation_cache()

    assert calls == {"related": 1, "unrelated": 0}


def test_prepare_processing_callable_caches_equivalent_bound_method_hooks() -> None:
    module_name = __name__

    class PreparedCallable:
        __name__ = "prepared_callable"
        __module__ = module_name

        calls = 0

        def __call__(self, image):
            return image

        def prepare(self) -> None:
            type(self).calls += 1

    first = PreparedCallable()
    second = PreparedCallable()
    first.__dict__[FunctionContractAttribute.processing_prepare] = first.prepare
    second.__dict__[FunctionContractAttribute.processing_prepare] = second.prepare

    reset_processing_callable_preparation_cache()

    prepare_processing_callable(first)
    prepare_processing_callable(second)

    assert PreparedCallable.calls == 1


def test_prepare_module_autoregister_families_skips_cellprofiler_backend_mixin_root() -> (
    None
):
    prepare_module_autoregister_families(
        "openhcs.processing.backends.cellprofiler.crop"
    )


def test_module_registered_family_preparation_runs_compiler_prepared_family_hook() -> (
    None
):
    global _AUTOREGISTER_PREPARED_TEST_FAMILY_CALLS
    _AUTOREGISTER_PREPARED_TEST_FAMILY_CALLS = 0
    AutoRegisterRegistryPreparation.cached_module_registry_families.cache_clear()

    report = AutoRegisterRegistryPreparation.prepare_module_registered_families(
        (sys.modules[__name__],)
    )

    assert _AUTOREGISTER_PREPARED_TEST_FAMILY_CALLS == 1
    assert report.prepared_family_count == 1
    assert _PreparedAutoRegisterImplementation in (
        _PreparedAutoRegisterFamily.__registry__.values()
    )


def test_callable_contract_preserves_immutable_runtime_batch_executors() -> None:
    contract = CallableContract.from_callable(_function_with_runtime_batch_executor)

    assert isinstance(contract.runtime_batch_executors, MappingProxyType)
    assert (
        contract.runtime_batch_executor(RuntimeBatchExecutionDomain.PURE_2D_SLICES)
        is _batch_executor
    )


def test_callable_contract_pickles_runtime_batch_executors() -> None:
    restored = pickle.loads(
        pickle.dumps(
            CallableContract.from_callable(_function_with_runtime_batch_executor)
        )
    )

    assert isinstance(restored.runtime_batch_executors, MappingProxyType)
    assert (
        restored.runtime_batch_executor(RuntimeBatchExecutionDomain.PURE_2D_SLICES)
        is _batch_executor
    )


def test_function_reference_preserves_batching_through_compiler_and_transport(
    monkeypatch,
) -> None:
    func = _function_with_runtime_batch_executor
    monkeypatch.setattr(func, "__dict__", dict(vars(func)))
    prepare_processing_callable(func)
    reference = FunctionReferenceTransportAuthority.function_reference(func)

    normalized = normalize_function_pattern(reference)
    contract = normalized.groups[0].items[0].contract
    restored = pickle.loads(pickle.dumps(contract))
    assert restored.func == reference
    expected_metadata = reference.metadata.with_prepared_signatures(func, func)
    assert restored.metadata.canonical_signature == expected_metadata.canonical_signature
    assert restored.metadata == expected_metadata
    assert restored.runtime_batch_executor(
        RuntimeBatchExecutionDomain.PURE_2D_SLICES
    ) is _batch_executor
    assert restored.runtime_batch_executor(
        RuntimeBatchExecutionDomain.MEASUREMENT_IMAGES
    ) is _measurement_batch_executor


def test_reference_batch_family_preserves_wrapper_precedence_and_raw_inheritance(
    monkeypatch,
) -> None:
    wrapper = _function_with_batch_override
    monkeypatch.setattr(wrapper, "__dict__", dict(vars(wrapper)))
    attach_callable_contract_metadata(
        wrapper,
        raw_processing_function=_function_with_runtime_batch_executor,
    )
    prepare_processing_callable(wrapper)
    reference = FunctionReferenceTransportAuthority.function_reference(wrapper)
    assert isinstance(
        reference.metadata.raw_processing_function, ImportableFunctionReference
    )

    contract = normalize_function_pattern(reference).groups[0].items[0].contract
    assert contract.runtime_batch_executor(
        RuntimeBatchExecutionDomain.PURE_2D_SLICES
    ) is _override_batch_executor
    assert contract.runtime_batch_executor(
        RuntimeBatchExecutionDomain.MEASUREMENT_IMAGES
    ) is _measurement_batch_executor


def test_registry_reference_preserves_real_intensity_batch_declarations() -> None:
    from openhcs.processing.backends.cellprofiler.intensity import (
        measure_object_intensity,
    )

    direct = CallableContract.from_callable(measure_object_intensity)
    reference = FunctionReferenceTransportAuthority.function_reference(
        measure_object_intensity
    )
    assert isinstance(reference, RegistryFunctionReference)
    contract = normalize_function_pattern(reference).groups[0].items[0].contract
    restored = pickle.loads(pickle.dumps(contract))

    for domain in (
        RuntimeBatchExecutionDomain.MEASUREMENT_IMAGES,
        RuntimeBatchExecutionDomain.PURE_2D_SLICES,
    ):
        executor = direct.runtime_batch_executor(domain)
        assert executor is not None
        assert restored.runtime_batch_executor(domain) is executor


def test_runtime_slice_batch_request_exposes_callable_defaults() -> None:
    def process(image, *, method="otsu", threshold=0.5):
        return image, method, threshold

    def execute_slice(func, image, kwargs, slice_index, slice_count):
        del slice_index, slice_count
        return func(image, **kwargs)

    request = RuntimePure2DSliceBatchRequest(
        func=process,
        slices_2d=("image",),
        kwargs={"threshold": 0.75},
        execute_slice=execute_slice,
    )

    assert request.kwargs["method"] == "otsu"
    assert request.kwargs["threshold"] == 0.75
    assert request.execute_one(0) == ("image", "otsu", 0.75)


def test_runtime_slice_batch_request_preserves_callable_result_identity() -> None:
    class MeasurementRows:
        pass

    rows = MeasurementRows()
    result = ("image", rows)

    request = RuntimePure2DSliceBatchRequest(
        func=lambda image: image,
        slices_2d=("image",),
        kwargs={},
        execute_slice=lambda func, image, kwargs, slice_index, slice_count: result,
    )

    assert request.execute_one(0) is result
