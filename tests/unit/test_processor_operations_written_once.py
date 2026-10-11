"""Processor operations are written once against arraybridge ``ArrayOperations``.

The six backend processor modules register shared operations from
``image_stack_operations``; a backend keeps its own body only where its
algorithm genuinely differs (L5 receipt census).
"""

from __future__ import annotations

import ast
import importlib
import inspect
from pathlib import Path

import numpy as np
import pytest
from arraybridge import MemoryType
from arraybridge.array_operations import ArrayOperations

from openhcs.core.callable_contract import CallableContract
from openhcs.core.processing_contracts import VolumetricToSliceContract
from openhcs.processing.backends.lib_registry.openhcs_registry import OpenHCSRegistry
from openhcs.processing.backends.processors import image_stack_operations
from openhcs.processing.backends.processors.method_axes import (
    SpatialBinMethod,
    StackProjectionMethod,
)

PROCESSOR_ROOT = Path(image_stack_operations.__file__).parent
BACKENDS = tuple(member.value for member in MemoryType)

# Census of L5: backend declarations whose algorithm genuinely differs from the
# other backends' and therefore keeps its own body.
OWN_BODIES = {
    "sharpen": set(BACKENDS),
    "tophat": set(BACKENDS),
    "stack_equalize_histogram": {"torch", "jax", "tensorflow", "pyclesperanto"},
    "percentile_normalize": {"torch", "jax", "tensorflow", "pyclesperanto"},
    "stack_percentile_normalize": {"torch", "jax", "tensorflow", "pyclesperanto"},
    "create_composite": {"numpy", "torch", "tensorflow", "pyclesperanto"},
    "create_linear_weight_mask": {"pyclesperanto"},
    "apply_mask": {"pyclesperanto"},
    "mean_projection": {"pyclesperanto"},
    "_gaussian_blur": {"torch", "jax", "tensorflow"},
}


def _processor_module(backend: str):
    return importlib.import_module(
        f"openhcs.processing.backends.processors.{backend}_processor"
    )


def _processor_trees() -> dict[str, ast.Module]:
    return {
        backend: ast.parse((PROCESSOR_ROOT / f"{backend}_processor.py").read_text())
        for backend in BACKENDS
    }


def _calls_shared_operation(function: ast.FunctionDef) -> bool:
    """Whether the body delegates to a shared operation (validation alone is not one)."""
    return any(
        isinstance(node, ast.Attribute)
        and isinstance(node.value, ast.Name)
        and node.value.id == "operations"
        and node.attr != "require_stack"
        for node in ast.walk(function)
    )


def test_each_backend_module_registers_with_its_own_leaf() -> None:
    for backend in BACKENDS:
        leaf = _processor_module(backend).OPERATIONS
        assert leaf is ArrayOperations.for_memory(MemoryType(backend))


def test_operations_shared_by_two_backends_are_written_once() -> None:
    definitions: dict[str, dict[str, ast.FunctionDef]] = {}
    for backend, tree in _processor_trees().items():
        for node in tree.body:
            if isinstance(node, ast.FunctionDef):
                definitions.setdefault(node.name, {})[backend] = node
    restated = {
        (name, backend)
        for name, by_backend in definitions.items()
        if len(by_backend) > 1
        for backend, function in by_backend.items()
        if backend not in OWN_BODIES.get(name, set())
        and not _calls_shared_operation(function)
    }
    assert not restated


def test_processor_modules_declare_no_dispatch_family_validator_or_gpu_switch() -> None:
    for backend, tree in _processor_trees().items():
        source = (PROCESSOR_ROOT / f"{backend}_processor.py").read_text()
        assert "OPENHCS_SUBPROCESS_NO_GPU" not in source, backend
        for node in tree.body:
            assert not (
                isinstance(node, ast.FunctionDef) and node.name == "_validate_3d_array"
            ), backend
            if isinstance(node, ast.ClassDef):
                bases = {ast.unparse(base) for base in node.bases}
                assert not any(
                    "StackProjectionMethod" in base or "SpatialBinMethod" in base
                    for base in bases
                ), (backend, node.name)
    assert not (PROCESSOR_ROOT / "percentile_utils.py").exists()


def test_projection_choices_are_served_by_the_projection_family() -> None:
    served = set(image_stack_operations.StackProjection.__registry__)
    assert served == {method.value for method in StackProjectionMethod}
    assert set(image_stack_operations.SpatialBin.__registry__) == {
        method.value for method in SpatialBinMethod
    }
    for backend in BACKENDS:
        create_projection = _processor_module(backend).create_projection
        method_type = type(inspect.signature(create_projection).parameters["method"].default)
        assert {member.value for member in method_type} <= served, backend


def test_numpy_registrations_compute_the_shared_operations() -> None:
    numpy_processor = _processor_module("numpy")
    stack = np.arange(2 * 4 * 4, dtype=np.uint16).reshape(2, 4, 4)

    assert numpy_processor.spatial_bin_2d(stack, 2, SpatialBinMethod.MEAN).shape == (2, 2, 2)
    np.testing.assert_array_equal(
        numpy_processor.spatial_bin_3d(stack, 2, SpatialBinMethod.MAX),
        stack.reshape(1, 2, 2, 2, 2, 2).max(axis=(1, 3, 5)),
    )
    for method, reduce in (
        (numpy_processor.NumpyStackProjectionMethod.MAX, np.max),
        (numpy_processor.NumpyStackProjectionMethod.MIN, np.min),
    ):
        np.testing.assert_array_equal(
            numpy_processor.create_projection(stack, method), reduce(stack, axis=0)
        )
    np.testing.assert_array_equal(
        numpy_processor.create_projection(stack, numpy_processor.NumpyStackProjectionMethod.MEAN),
        stack.mean(axis=0).astype(stack.dtype),
    )
    assert (
        CallableContract.from_callable(numpy_processor.create_projection)
        .require_processing_contract()
        is VolumetricToSliceContract
    )
    mask = np.array([[1, 0, 1, 0]] * 4, dtype=np.uint16)
    np.testing.assert_array_equal(numpy_processor.apply_mask(stack, mask), stack * mask)
    with pytest.raises(ValueError, match="3D array"):
        numpy_processor.max_projection(stack[0])


def test_jax_registrations_match_numpy() -> None:
    jnp = pytest.importorskip("jax.numpy")
    numpy_processor = _processor_module("numpy")
    jax_processor = _processor_module("jax")
    stack = np.random.default_rng(0).integers(0, 4000, (3, 8, 10)).astype(np.uint16)
    for name in ("max_projection", "mean_projection"):
        np.testing.assert_array_equal(
            np.asarray(getattr(jax_processor, name)(jnp.asarray(stack))),
            getattr(numpy_processor, name)(stack),
        )
    np.testing.assert_allclose(
        np.asarray(jax_processor.create_linear_weight_mask(12, 9)),
        numpy_processor.create_linear_weight_mask(12, 9),
        rtol=1e-6,
    )


def test_registry_discovery_does_not_replace_public_processor_callables() -> None:
    numpy_processor = _processor_module("numpy")
    declared_projection = numpy_processor.create_projection
    registry = OpenHCSRegistry()
    registry.MODULES_TO_SCAN = [numpy_processor.__name__]

    functions = registry.discover_functions()

    assert numpy_processor.create_projection is declared_projection
    assert (
        functions["processors_numpy_processor_create_projection"].func
        is not declared_projection
    )
