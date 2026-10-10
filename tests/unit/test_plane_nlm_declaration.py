"""Independent-plane NLM uses the original contract, kernel and source owners."""

from __future__ import annotations

import inspect
from dataclasses import replace
from importlib import import_module

import numpy as np
import pytest
from skimage import restoration

from openhcs.agent.services.pipeline_authoring_service import (
    InvalidFunctionKwargsError,
    _validate_callable_kwargs,
)
from openhcs.core.callable_contract import CallableContract
from openhcs.core.function_reference import (
    FunctionReferenceTransportAuthority,
    RegistryFunctionReference,
)
from openhcs.core.memory import numpy as numpy_contract
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.processing.backends.lib_registry.openhcs_registry import OpenHCSRegistry
from openhcs.processing.backends.lib_registry.scikit_image_registry import SkimageRegistry
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.processing.backends.processors.numpy_processor import (
    non_local_means_denoise_planes,
)


NLM_KWARGS = dict(
    patch_size=3, patch_distance=2, h=0.075,
    fast_mode=True, sigma=0.0, preserve_range=True,
)


def _source(plane_count):
    rng = np.random.default_rng(458)
    pixels = rng.uniform(0.1, 0.9, (plane_count, 16, 20)).astype(np.float32)
    provenance = SourceImageProvenancePlanes.from_components(
        paths=tuple(f"/synthetic/A01_s{site + 1}_w1.tif" for site in range(plane_count)),
        component_metadata=tuple(
            {"well": "A01", "site": str(site + 1), "channel": "1"}
            for site in range(plane_count)
        ),
    )
    provenance = SourceImageProvenancePlanes(tuple(
        replace(plane, source_image_name="C1") for plane in provenance.planes
    ))
    metadata = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_names=("C1",) * plane_count,
        source_image_provenance_planes=provenance,
        source_plane_dtypes=("float32",) * plane_count,
        source_voxel_spacing=SourceVoxelSpacing((0.5, 0.75)),
        source_spatial_domain=SourceSpatialDomain(
            origin_yx=(0, 0), source_shape_yx=(16, 20),
        ),
    )
    return metadata.payload_with(pixels)


def _registered(func=non_local_means_denoise_planes):
    metadata = OpenHCSRegistry.metadata_for_declared_callable(func)
    assert metadata is not None
    assert metadata.contract is ProcessingContract.PURE_2D
    return metadata


@pytest.mark.parametrize("plane_count", (1, 3))
@pytest.mark.parametrize("fast_mode", (True, False))
def test_real_nlm_kernel_receives_only_planes_and_restores_context(
    monkeypatch, plane_count, fast_mode,
):
    source = _source(plane_count)
    before = source.data.copy()
    original = restoration.denoise_nl_means
    kwargs = dict(NLM_KWARGS, fast_mode=fast_mode)
    expected = np.stack([original(plane, channel_axis=None, **kwargs) for plane in before])
    seen = []

    def observed_kernel(image, **kernel_kwargs):
        seen.append((image.shape, image.dtype, image.nbytes, kernel_kwargs))
        return original(image, **kernel_kwargs)

    monkeypatch.setattr(restoration, "denoise_nl_means", observed_kernel)
    result = _registered().func(source, **kwargs)
    assert seen == [((16, 20), np.dtype("float32"), 1280, dict(kwargs, channel_axis=None))] * plane_count
    np.testing.assert_array_equal(result.data, expected)
    np.testing.assert_array_equal(source.data, before)
    assert result.data.dtype == expected.dtype == np.dtype("float32")
    assert result.data.shape == (plane_count, 16, 20)
    current = result.metadata
    prior = source.metadata
    assert current.plane_axis is prior.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
    assert current.source_voxel_spacing == prior.source_voxel_spacing
    assert current.source_spatial_domain == prior.source_spatial_domain
    assert current.source_image_provenance_planes.identity == prior.source_image_provenance_planes.identity
    assert current.source_image_names == prior.source_image_names


@pytest.mark.parametrize("shape", ((1, 16, 20), (3, 16, 20), (16, 20, 3)))
def test_bare_volume_or_color_array_is_not_guessed_or_squeezed(shape):
    with pytest.raises(ValueError, match="Plane NLM requires a 2-D grayscale plane"):
        _registered().func(np.zeros(shape, dtype=np.float32), **NLM_KWARGS)


def test_original_volumetric_nlm_still_receives_the_whole_volume(monkeypatch):
    source = _source(3)
    before = source.data.copy()
    original = restoration.denoise_nl_means
    expected = original(before, channel_axis=None, **NLM_KWARGS)
    module = import_module("skimage.restoration.non_local_means")
    original_kernel = module._fast_nl_means_denoising_3d
    seen = []

    def observed_volume(image, *args, **kwargs):
        seen.append(image.shape)
        return original_kernel(image, *args, **kwargs)

    monkeypatch.setattr(module, "_fast_nl_means_denoising_3d", observed_volume)
    registry = SkimageRegistry()
    adapter = registry.create_library_adapter(original, ProcessingContract.FLEXIBLE)
    volume = registry.apply_contract_wrapper(adapter, ProcessingContract.FLEXIBLE)
    result = volume(source, channel_axis=None, **NLM_KWARGS)
    # scikit-image appends its channel singleton; all three spatial axes remain.
    assert seen == [(3, 16, 20, 1)]
    np.testing.assert_array_equal(result.data, expected)
    np.testing.assert_array_equal(source.data, before)


def test_declared_catalog_identity_and_public_kwargs_are_original_projections():
    metadata = _registered()
    function_id = f"{metadata.registry.library_name}:{metadata.name}"
    assert function_id == "openhcs:processors_numpy_processor_non_local_means_denoise_planes"
    assert metadata.original_name == "non_local_means_denoise_planes"
    assert "slice_by_slice" not in inspect.signature(metadata.func).parameters
    _validate_callable_kwargs(function_id, metadata.func, NLM_KWARGS)
    CallableContract.from_callable(metadata.func).validate_public_kwargs(NLM_KWARGS)
    for forbidden in ("slice_by_slice", "channel_axis", "plane_axis", "guess_axis"):
        with pytest.raises(InvalidFunctionKwargsError, match="Invalid kwargs"):
            _validate_callable_kwargs(function_id, metadata.func, {forbidden: True})


def test_nominal_transport_resolves_original_declaration_without_global_catalog():
    metadata = _registered()
    reference = FunctionReferenceTransportAuthority.function_reference(metadata.func)
    assert isinstance(reference, RegistryFunctionReference)
    assert reference.composite_key == "openhcs:processors_numpy_processor_non_local_means_denoise_planes"
    resolved = reference.resolve()
    assert CallableContract.from_callable(resolved).processing_contract is ProcessingContract.PURE_2D
    result = resolved(_source(1), **NLM_KWARGS)
    assert result.data.shape == (1, 16, 20)


def test_new_independent_declaration_executes_same_consumer_without_edits():
    seen = []

    @numpy_contract(contract=ProcessingContract.PURE_2D)
    def independent_plane_offset(image: np.ndarray, *, offset: float = 0.25) -> np.ndarray:
        seen.append(image.shape)
        return image + offset

    source = _source(3)
    result = _registered(independent_plane_offset).func(source, offset=0.5)
    assert seen == [(16, 20)] * 3
    np.testing.assert_array_equal(result.data, source.data + 0.5)
    assert result.metadata.source_image_provenance_planes.identity == (
        source.metadata.source_image_provenance_planes.identity
    )


def test_flexible_existing_mro_selects_original_per_plane_behavior():
    source = _source(3)
    seen = []

    @numpy_contract
    def independent_flexible_offset(image: np.ndarray) -> np.ndarray:
        seen.append(image.shape)
        return image + 0.5

    wrapped = OpenHCSRegistry.metadata_for_declared_callable(independent_flexible_offset).func
    result = wrapped(source, slice_by_slice=True)
    assert seen == [(16, 20)] * 3
    np.testing.assert_array_equal(result.data, source.data + 0.5)
    seen.clear()
    result = wrapped(source, slice_by_slice=False)
    assert seen == [(3, 16, 20)]
    np.testing.assert_array_equal(result.data, source.data + 0.5)
