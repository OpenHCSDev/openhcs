"""Storage reduction preserves its generic oracle and compiled backend domains."""

import os
import subprocess
import sys
import textwrap
import warnings
from pathlib import Path

import numpy as np
import pytest

from openhcs.core.runtime_object_labels import (
    ObjectLabelPayload,
    ObjectLabelStorageStrategy,
    ObjectLabelVariantData,
    object_label_axis_centers,
)
from openhcs.core.runtime_sparse_labels import SparseIJVLabelRows


def generic_centers(labels, domain):
    return ObjectLabelStorageStrategy.axis_centers(
        ObjectLabelStorageStrategy.for_value(labels), labels, domain=domain
    )


def assert_centers(actual, expected):
    for actual_array, expected_array in zip(
        (*actual[0], actual[1]), (*expected[0], expected[1]), strict=True
    ):
        np.testing.assert_array_equal(actual_array, expected_array)
        assert actual_array.tobytes() == expected_array.tobytes()
        assert actual_array.dtype == expected_array.dtype
        assert actual_array.strides == expected_array.strides
        assert actual_array.flags.owndata == expected_array.flags.owndata
        assert actual_array.base is None
    assert not np.shares_memory(*actual[0][:2])


@pytest.mark.parametrize("wrapped", (False, True))
@pytest.mark.parametrize("shape", ((4, 5), (3, 4, 5)))
def test_dense_storage_reduces_without_sparse_materialization(monkeypatch, wrapped, shape):
    labels = np.zeros(shape, dtype=np.int32)
    labels[..., 1:3, 2:4] = 1
    labels[..., 3, 0] = 4
    domain = (1, 2, 4, 7)
    expected = generic_centers(labels, domain)
    value = (
        ObjectLabelPayload(variant_data=ObjectLabelVariantData(labels=labels))
        if wrapped else labels
    )
    before = labels.copy()

    def reject_materialization(_cls, _labels):
        raise AssertionError("Coordinate reduction materialized sparse pixels")

    monkeypatch.setattr(SparseIJVLabelRows, "from_dense_stack", classmethod(reject_materialization))
    assert_centers(object_label_axis_centers(value, domain=domain), expected)
    np.testing.assert_array_equal(labels, before)


@pytest.mark.parametrize("layout", ("c", "f", "view", "readonly", "empty"))
def test_layout_and_mutable_pixels_preserve_generic_result(layout):
    labels = np.arange(30, dtype=np.int32).reshape(5, 6) % 5
    if layout == "f":
        labels = np.asfortranarray(labels)
    elif layout == "view":
        labels = labels[::-1, ::2]
    elif layout == "readonly":
        labels.flags.writeable = False
    elif layout == "empty":
        labels = np.zeros((2, 0, 3), dtype=np.int32)
    domain = (1, 2, 4, 9)
    assert_centers(object_label_axis_centers(labels, domain=domain), generic_centers(labels, domain))
    if labels.size and labels.flags.writeable:
        labels.flat[0] = 4
        assert_centers(object_label_axis_centers(labels, domain=domain), generic_centers(labels, domain))


@pytest.mark.parametrize("dtype", (np.bool_, np.float64, np.int64, np.uint64))
def test_other_dtype_conversion_and_warning_policy_stays_generic(dtype):
    labels = np.array([[0, 1], [2, 3]], dtype=dtype)
    if dtype is np.float64:
        labels[0] = (0.5, np.nan)
    elif dtype is np.uint64:
        labels[0, 1] = 2**32 + 1
    outcomes = []
    for call in (generic_centers, lambda x, domain: object_label_axis_centers(x, domain=domain)):
        with warnings.catch_warnings(record=True) as observed:
            warnings.simplefilter("always")
            try:
                result = call(labels, (1, 2, 3, 8))
            except ValueError as error:
                result = (type(error), str(error))
        outcomes.append((result, [(type(w.message), str(w.message)) for w in observed]))
    if dtype is np.uint64:
        assert outcomes[0][0] == outcomes[1][0]
    else:
        assert_centers(outcomes[0][0], outcomes[1][0])
    assert outcomes[0][1] == outcomes[1][1]


def test_sparse_overlap_and_subtype_keep_existing_representation():
    sparse = SparseIJVLabelRows(np.array([[0, 0, 1], [0, 0, 2], [2, 3, 1]], dtype=np.int32))
    assert_centers(object_label_axis_centers(sparse, domain=(1, 2, 4)), generic_centers(sparse, (1, 2, 4)))

    class DenseSubtype(np.ndarray):
        @property
        def dtype(self):
            raise AssertionError("Subtype properties must not be probed before generic coercion")

    subtype = np.array([[1, 0], [2, 2]], dtype=np.int32).view(DenseSubtype)
    assert_centers(object_label_axis_centers(subtype, domain=(1, 2, 4)), generic_centers(subtype, (1, 2, 4)))


@pytest.mark.parametrize("shape", ((), (4,), (2, 3, 4, 5)))
def test_invalid_shape_keeps_original_error(shape):
    labels = np.zeros(shape, dtype=np.int32)
    with pytest.raises(ValueError) as original:
        generic_centers(labels, (1,))
    with pytest.raises(type(original.value), match="SparseIJVLabelRows.from_dense_stack") as current:
        object_label_axis_centers(labels, domain=(1,))
    assert str(current.value) == str(original.value)


@pytest.mark.parametrize("failure", (None, "iterate", 1, 2, 3, 4, 5))
def test_domain_callbacks_follow_pixel_snapshot_and_original_allocation_order(failure):
    outcomes = []
    for call in (generic_centers, lambda labels, domain: object_label_axis_centers(labels, domain=domain)):
        labels = np.array([[1, 1], [2, 0]], dtype=np.int32)
        effects = []

        class DomainInteger(int):
            def __gt__(self, other):
                effects.append("compare")
                return super().__gt__(other)

            def __add__(self, other):
                effects.append("add")
                result = super().__add__(other)
                return float(result) if effects.count("add") == failure else result

        class MutatingDomain:
            def __iter__(self):
                effects.append("iterate")
                labels[:] = 3
                labels.shape = (1, 2, 2)
                if failure == "iterate":
                    raise RuntimeError("Domain iteration failed after changing pixels")
                yield DomainInteger(4)

        try:
            result = call(labels, MutatingDomain())
        except (RuntimeError, TypeError) as error:
            outcome = (type(error), str(error))
        else:
            outcome = result
        outcomes.append((outcome, effects, labels.copy()))

    if failure is None:
        assert_centers(outcomes[0][0], outcomes[1][0])
        np.testing.assert_array_equal(outcomes[1][0][1], (0, 2, 1, 0, 0))
        assert len(outcomes[1][0][0]) == 2
    else:
        assert outcomes[0][0] == outcomes[1][0]
    assert outcomes[0][1] == outcomes[1][1]
    np.testing.assert_array_equal(outcomes[0][2], outcomes[1][2])


@pytest.mark.parametrize("domain", ((4.0,), (np.int64(np.iinfo(np.int64).max),), (2**63,)))
def test_domain_minlength_errors_and_warnings_remain_numpy_owned(domain):
    outcomes = []
    for call in (generic_centers, lambda labels, domain: object_label_axis_centers(labels, domain=domain)):
        with warnings.catch_warnings(record=True) as observed:
            warnings.simplefilter("always")
            try:
                call(np.array([[1, 0], [2, 1]], dtype=np.int32), domain)
            except (TypeError, ValueError, OverflowError) as error:
                outcome = (type(error), str(error))
            else:
                raise AssertionError("Invalid minlength unexpectedly succeeded")
        outcomes.append((outcome, [(type(w.message), str(w.message)) for w in observed]))
    assert outcomes[0] == outcomes[1]


def test_invalid_geometry_precedes_domain_iteration():
    for call in (generic_centers, lambda labels, domain: object_label_axis_centers(labels, domain=domain)):
        effects = []

        class Domain:
            def __iter__(self):
                effects.append("iterate")
                yield 1

        with pytest.raises(ValueError, match="SparseIJVLabelRows.from_dense_stack"):
            call(np.zeros((2, 3, 4, 5), dtype=np.int32), Domain())
        assert not effects


def test_primary_objects_preparation_readies_all_admitted_storage_signatures(tmp_path):
    script = textwrap.dedent("""
        from unittest.mock import patch
        import numpy as np
        from openhcs.core.callable_contract import prepare_processing_callable
        from openhcs.core.runtime_object_labels import (
            _dense_label_coordinate_moments_numba, dense_label_centers_2d_numba,
            object_label_axis_centers,
        )
        from openhcs.processing.backends.cellprofiler.primary_objects import identify_primary_objects
        assert not _dense_label_coordinate_moments_numba.signatures
        prepare_processing_callable(identify_primary_objects)
        kernels = (_dense_label_coordinate_moments_numba, dense_label_centers_2d_numba)
        signatures = tuple(tuple(kernel.signatures) for kernel in kernels)
        assert all(signatures)

        def reject_compilation(signature):
            raise AssertionError(('Late coordinate compilation', str(signature)))

        with patch.object(_dense_label_coordinate_moments_numba, 'compile',
                          side_effect=reject_compilation), patch.object(
                dense_label_centers_2d_numba, 'compile', side_effect=reject_compilation):
            for shape in ((4, 5), (3, 4, 5)):
                base = np.arange(np.prod(shape), dtype=np.int32).reshape(shape) % 4
                for labels in (base, np.asfortranarray(base), base[..., ::-1], base.copy()):
                    object_label_axis_centers(labels, domain=(1, 2, 3, 6))
                    labels.flags.writeable = False
                    object_label_axis_centers(labels, domain=(1, 2, 3, 6))
        assert tuple(tuple(kernel.signatures) for kernel in kernels) == signatures
    """)
    environment = os.environ.copy()
    environment.update(OPENHCS_CPU_ONLY="true", NUMBA_CACHE_DIR=str(tmp_path / "kernels"))
    result = subprocess.run(
        (sys.executable, "-c", script), cwd=Path(__file__).parents[2],
        env=environment, capture_output=True, text=True, timeout=120,
    )
    assert result.returncode == 0, result.stdout + result.stderr
