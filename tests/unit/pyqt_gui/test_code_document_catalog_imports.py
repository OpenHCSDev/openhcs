"""Code-mode imports retain the endpoint's compiler contract and selected wrapper."""

import builtins
from contextlib import nullcontext
from unittest.mock import Mock

import pytest
from arraybridge import DtypeConversion
from arraybridge.decorators import SliceBySliceRuntimeParameter
from objectstate.object_state import ObjectStateRegistry

from openhcs.agent.services.function_catalog_service import FunctionCatalogServiceABC
from openhcs.core.callable_contract import CallableImportIdentity, CallableMetadata
from openhcs.core.config import LazyDtypeConfig
from openhcs.core.function_reference import (
    FunctionReferenceTransportAuthority,
    RegistryFunctionReference,
)
from openhcs.core.function_step_document import FunctionStepDocumentAuthority
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.processing.backends.processors.numpy_processor import (
    stack_percentile_normalize,
    tophat,
)
from openhcs.pyqt_gui.services.pipeline_object_state_binding import (
    PipelineObjectStateBinding,
)
from openhcs.pyqt_gui.services.ui_agent_bridge import (
    UiCodeDocumentExecutionService,
    UiCodeDocumentSourcePolicy,
    UiCodeDocumentValidationError,
)
from openhcs.ui.shared.plate_manager_code_document import (
    PlateManagerCodeDocumentAuthority,
)


@pytest.fixture
def catalog():
    service = Mock(spec=FunctionCatalogServiceABC)
    reference = RegistryFunctionReference(
        import_identity=CallableImportIdentity(
            module_name="skimage.filters.edges", function_name="sobel"
        ),
        composite_key="skimage:filters.sobel",
        metadata=CallableMetadata(
            input_memory_type="numpy",
            output_memory_type="numpy",
            execution_memory_type="numpy",
            processing_contract=ProcessingContract.FLEXIBLE,
            runtime_bound_parameters=(SliceBySliceRuntimeParameter,),
        ),
    )
    service.reference.return_value = reference
    service.get_by_import_path.return_value.entry.function_id = reference.composite_key
    return service


def source(imports="from skimage.filters.edges import sobel", name="sobel"):
    return (
        f"{imports}\n"
        "from openhcs.core.steps.function_step import FunctionStep\n"
        "from openhcs.core.config import GlobalPipelineConfig, PipelineConfig\n"
        "plate_paths = ['/tmp/plate']\n"
        "global_config = GlobalPipelineConfig()\n"
        "per_plate_configs = {'/tmp/plate': PipelineConfig()}\n"
        f"pipeline_data = {{'/tmp/plate': [FunctionStep(func={name}, name='Edges')]}}\n"
    )


@pytest.mark.parametrize("alias", ["sobel", "edge_filter", "Sobel"])
def test_catalog_import_preserves_selected_registry_wrapper(
    catalog, monkeypatch, alias
):
    original_import = builtins.__import__

    def guarded_import(name, *args, **kwargs):
        assert not name.startswith(
            "skimage"
        ), "Authoring must not import the processing library"
        return original_import(name, *args, **kwargs)

    with monkeypatch.context() as validation_guard:
        validation_guard.setattr(builtins, "__import__", guarded_import)
        assert UiCodeDocumentSourcePolicy(catalog).validate(source()) == ()
    operations = Mock()
    operations.patch_lazy_constructors.side_effect = nullcontext
    operations.migrate_code_namespace.return_value = None
    executor = UiCodeDocumentExecutionService(UiCodeDocumentSourcePolicy(catalog))
    result = executor.validate_source(
        source(f"from skimage.filters.edges import sobel as {alias}", alias), operations
    )
    resolved = result.pipeline_data["/tmp/plate"][0].func
    assert resolved is catalog.reference.return_value.resolve()
    transported = FunctionReferenceTransportAuthority.function_reference(resolved)
    assert transported.composite_key == catalog.reference.return_value.composite_key
    assert transported.metadata.processing_contract is ProcessingContract.FLEXIBLE
    assert SliceBySliceRuntimeParameter in transported.metadata.runtime_bound_parameters
    rendered = PlateManagerCodeDocumentAuthority.render(result)
    repeated = executor.validate_source(rendered, operations)
    assert repeated.pipeline_data["/tmp/plate"][0].func is resolved


@pytest.mark.parametrize(
    "imports,name",
    [
        ("from skimage.filters.edges import unknown", "unknown"),
        ("from skimage.filters.edges import *", "sobel"),
        ("from .openhcs import sobel", "sobel"),
        ("import skimage.filters.edges", "skimage"),
    ],
)
def test_catalog_does_not_authorize_library_roots_or_unlisted_names(
    catalog, imports, name
):
    assert any(
        error.code == "unsafe_import"
        for error in UiCodeDocumentSourcePolicy(catalog).validate(source(imports, name))
    )


def test_catalog_function_cannot_be_called_during_source_evaluation(catalog):
    errors = UiCodeDocumentSourcePolicy(catalog).validate(
        source("from skimage.filters.edges import sobel as Sobel", "Sobel()")
    )
    assert any(error.code == "unsafe_call" for error in errors)


def test_unlisted_import_fails_before_execution(catalog):
    catalog.get_by_import_path.return_value = None
    operations = Mock()
    with pytest.raises(UiCodeDocumentValidationError):
        UiCodeDocumentExecutionService(
            UiCodeDocumentSourcePolicy(catalog)
        ).validate_source(source(), operations)
    operations.patch_lazy_constructors.assert_not_called()
    catalog.reference.assert_not_called()


@pytest.mark.parametrize("entry", [tophat, (tophat, {"selem_radius": 3}), [tophat]])
def test_grouped_single_and_chained_functions_survive_object_state_round_trip(entry):
    ObjectStateRegistry.clear()
    try:
        step = FunctionStep(func={"1": [tophat], "2": entry})
        PipelineObjectStateBinding.update_plate_steps("/tmp/grouped-plate", [step])
        reconstructed = PipelineObjectStateBinding.steps_for_plate("/tmp/grouped-plate")
        assert reconstructed[0].same_declaration(step)
    finally:
        ObjectStateRegistry.clear()


def test_explicit_function_dtype_override_survives_object_state_round_trip():
    ObjectStateRegistry.clear()
    try:
        dtype_config = LazyDtypeConfig(default_dtype_conversion=DtypeConversion.UINT16)
        step = FunctionStep(
            func=(stack_percentile_normalize, {"dtype_config": dtype_config})
        )
        PipelineObjectStateBinding.update_plate_steps("/tmp/dtype-plate", [step])
        reconstructed = PipelineObjectStateBinding.steps_for_plate("/tmp/dtype-plate")[
            0
        ]
        assert (
            reconstructed.func[1]["dtype_config"].default_dtype_conversion
            is DtypeConversion.UINT16
        )
        rendered = FunctionStepDocumentAuthority.render(
            FunctionStepDocumentAuthority.from_value(reconstructed)
        )
        reparsed = FunctionStepDocumentAuthority.from_source(rendered).step
        assert (
            reparsed.func[1]["dtype_config"].default_dtype_conversion
            is DtypeConversion.UINT16
        )
    finally:
        ObjectStateRegistry.clear()
