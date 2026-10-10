"""Current intensity units survive composition, projection and native storage."""

from dataclasses import dataclass

import numpy as np
import pytest

from openhcs.core.aligned_image_payload import (
    ImagePayloadBundleContext, ImagePayloadStackContext, stack_image_payloads,
    ImagePayloadStackComposition,
)
from openhcs.core.image_file_serialization import ImageFileFormat, ImageFileSourceMetadata
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    ImagePayloadMetadataCompositionMode,
    ImageUnitIntervalIntensityMetadata,
)
from openhcs.core.source_bindings import NamedSourceBinding
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.payload_axes import PayloadAxes


def source(data, *, scale=255, channel_axis=None):
    return ImagePayloadMetadata(
        source_path='/declared/source.tif', source_dtype=str(data.dtype),
        intensity_scale=scale, axes=PayloadAxes.colour_samples(channel_axis),
        source_spatial_domain=SourceSpatialDomain((3, 5), (2, 3), 0, 'Source'),
        source_voxel_spacing=SourceVoxelSpacing((0.5, 0.5)),
    ).payload_with(data, np.array([[True, False, True], [True, True, False]]))


@pytest.mark.parametrize('reverse', (False, True))
@pytest.mark.parametrize('color', ('replicated', 'distinct'))
@pytest.mark.parametrize('mode', tuple(ImagePayloadMetadataCompositionMode))
def test_original_source_binding_composition_and_selected_cp_units(reverse, color, mode):
    from openhcs.interop.cellprofiler.image_normalization import normalize_cellprofiler_image_payload

    scalar = np.full((2, 3), 128, dtype=np.uint8)
    rgb = np.repeat(scalar[..., None], 3, axis=-1)
    if color == 'distinct':
        rgb[..., 1] = 32
        rgb[..., 2] = 240
    binding = NamedSourceBinding(alias='Source', load_as_monochrome=True)
    inputs = [binding.apply_loaded_payload(source(scalar), None),
              binding.apply_loaded_payload(source(rgb, channel_axis=-1), None)]
    if reverse:
        inputs.reverse()
    stacked = stack_image_payloads(inputs, metadata_mode=mode)
    for index, original in enumerate(inputs):
        selected = stacked.metadata.for_leading_source_plane(index).payload_with(
            stacked.data[index], stacked.mask[index],
        )
        expected = normalize_cellprofiler_image_payload(original)
        actual = normalize_cellprofiler_image_payload(selected)
        np.testing.assert_allclose(actual.data, expected.data)
        np.testing.assert_array_equal(actual.mask, original.mask)
        assert actual.metadata.source_image_names == ('Source',)
        assert actual.metadata.intensity_scale == 255
        assert actual.metadata.source_voxel_spacing == original.metadata.source_voxel_spacing
        actual_domain = actual.metadata.source_spatial_domain
        original_domain = original.metadata.source_spatial_domain
        assert actual_domain.origin_yx == original_domain.origin_yx
        assert actual_domain.source_shape_yx == original_domain.source_shape_yx
        assert actual_domain.fill_value == original_domain.fill_value


@pytest.mark.parametrize('reverse', (False, True))
def test_raw_heterogeneous_declared_scales_survive_integer_float_promotion(reverse):
    inputs = [source(np.full((2, 3), 30, dtype=np.uint8), scale=60),
              source(np.full((2, 3), 15, dtype=np.float32), scale=30)]
    if reverse:
        inputs.reverse()
    stack = stack_image_payloads(inputs, metadata_mode=ImagePayloadMetadataCompositionMode.STACK)
    assert stack.metadata.unit_interval_intensity is None
    np.testing.assert_allclose(stack.normalize_intensity_payload(), 0.5)
    for index, original in enumerate(inputs):
        projected = stack.metadata.for_leading_source_plane(index).payload_with(
            stack.data[index])
        np.testing.assert_array_equal(projected.normalize_intensity_payload(),
                                      original.normalize_intensity_payload())


def test_normalized_and_remapped_float_pixels_do_not_reenter_source_codes():
    normalized = (source(np.full((2, 3), 128, dtype=np.uint8))).normalize_intensity_payload()
    remapped = normalized.metadata.without_unit_interval_intensity_scale().payload_with(
        normalized.data * 4 - 1, normalized.mask,
    )
    for payload in (normalized, remapped):
        np.testing.assert_array_equal(payload.normalize_intensity_payload(), payload)
        assert payload.normalize_intensity_payload().metadata == payload.metadata


def test_unscaled_analytical_float_uses_no_observed_range_or_guessed_factor():
    pixels = np.array([[-3.5, 800.0], [0.25, 2.0]], dtype=np.float32)
    np.testing.assert_array_equal(pixels.normalize_intensity_payload(), pixels)


@pytest.mark.parametrize('scale', (0, -1, float('nan'), float('inf')))
def test_invalid_declared_scale_is_rejected(scale):
    with pytest.raises(ValueError, match='finite and positive'):
        (source(np.ones((2, 3), dtype=np.float32), scale=scale)).normalize_intensity_payload()


def test_native_pixel_conversion_resets_current_domain_and_float_roundtrip_preserves_it(tmp_path):
    normalized = (source(np.full((2, 3), 128, dtype=np.uint8))).normalize_intensity_payload()
    metadata = normalized.metadata
    native = ImageFileSourceMetadata(np.dtype('uint8'), 255).project_image_metadata(
        metadata, values_preserved=False,
    )
    assert native.unit_interval_intensity is None
    np.testing.assert_allclose((native.payload_with(np.full((2, 3), 128, dtype=np.uint8))).normalize_intensity_payload(), normalized)
    path = tmp_path / 'analytical.npy'
    image_format = ImageFileFormat.require_path(path)
    image_format.write(path, normalized)
    restored = image_format.persisted_metadata(path, normalized)
    assert restored.unit_interval_intensity == metadata.unit_interval_intensity
    np.testing.assert_array_equal((restored.payload_with(image_format.read(path))).normalize_intensity_payload(), normalized)
    assert restored.source_spatial_domain == metadata.source_spatial_domain
    assert restored.source_voxel_spacing == metadata.source_voxel_spacing


@pytest.mark.parametrize('reverse', (False, True))
def test_independent_normalization_and_composition_capabilities_use_cooperative_mro(reverse):
    calls = []

    class NormalizationAudit:
        def normalize_intensity_payload(self, payload, **kwargs):
            calls.append('normalization')
            return super().normalize_intensity_payload(payload, **kwargs)

    @dataclass
    class DeclaredMetadata(NormalizationAudit, ImagePayloadMetadata):
        pass

    class PixelAudit:
        def compose_unmasked(self, payloads, **kwargs):
            calls.append('pixels')
            return super().compose_unmasked(payloads, **kwargs)

    class MaskAudit:
        def compose_mask(self, data, metadata):
            calls.append('mask')
            return super().compose_mask(data, metadata)

    capabilities = (MaskAudit, PixelAudit) if reverse else (PixelAudit, MaskAudit)

    class DeclaredComposition(*capabilities, ImagePayloadStackContext):
        pass

    raw = DeclaredMetadata(intensity_scale=64, source_dtype='uint8').payload_with(
        np.full((2, 3), 32, dtype=np.uint8))
    processed = ImagePayloadMetadata(unit_interval_intensity=ImageUnitIntervalIntensityMetadata()).payload_with(
        np.full((2, 3), 0.5, dtype=np.float32))
    result = DeclaredComposition((raw, processed), ImagePayloadMetadataCompositionMode.STACK).compose()
    np.testing.assert_array_equal(result.data, 0.5)
    assert calls == ['normalization', 'pixels', 'mask']
    assert DeclaredMetadata.__mro__[:3] == (DeclaredMetadata, NormalizationAudit, ImagePayloadMetadata)


def test_bundle_leaf_cooperates_with_shared_intensity_and_pixel_owners():
    raw = source(np.full((2, 3), 128, dtype=np.uint8))
    normalized = raw.normalize_intensity_payload()
    result = ImagePayloadBundleContext.from_payloads((raw, normalized)).compose()
    np.testing.assert_array_equal(result.data[0], normalized.data)
    np.testing.assert_array_equal(result.mask, raw.mask)


def test_saved_output_context_retains_the_independent_composed_buffer_domain():
    raw = source(np.full((2, 3), 128, dtype=np.uint8))
    normalized = raw.normalize_intensity_payload()
    inputs = (raw, normalized)
    copied = stack_image_payloads(inputs, metadata_mode=ImagePayloadMetadataCompositionMode.STACK)
    restored = ImagePayloadStackComposition.with_saved_output_context(
        copied, inputs, tuple(value.metadata for value in inputs),
        single_output_plane_axis=None,
    )
    assert restored.data is copied.data
    for index in (0, 1):
        selected = restored.metadata.for_leading_source_plane(index).payload_with(
            restored.data[index])
        np.testing.assert_array_equal(selected.normalize_intensity_payload(), normalized)
        assert selected.metadata.has_normalized_intensity


def test_common_quantization_requires_every_current_plane_not_only_known_members():
    raw = source(np.full((2, 3), 128, dtype=np.uint8))
    normalized = raw.normalize_intensity_payload()
    remapped = normalized.metadata.without_unit_interval_intensity_scale().payload_with(
        np.full((2, 3), 0.123456, dtype=np.float32))
    mixed = stack_image_payloads((raw, remapped), metadata_mode=ImagePayloadMetadataCompositionMode.STACK)
    assert mixed.metadata.common_unit_interval_intensity_scale() is None
    assert mixed.metadata.for_leading_source_plane(0).unit_interval_intensity_scale == 255


@pytest.mark.parametrize('normalized', (False, True))
def test_proof_invalidation_preserves_the_current_numerical_domain(normalized):
    from openhcs.processing.backends.cellprofiler.color import (
        color_to_gray_combine_output_metadata,
    )

    raw = source(np.full((2, 3), 128, dtype=np.uint8))
    payload = raw.normalize_intensity_payload() if normalized else raw
    # Use the original arithmetic output metadata owner, not a test-side marker.
    metadata = color_to_gray_combine_output_metadata(payload)
    transformed = metadata.payload_with(
        payload.data.astype(np.float32) * 0.5,
        payload.mask,
    )
    assert metadata.has_normalized_intensity is normalized
    assert metadata.unit_interval_intensity_scale is None
    expected = payload.data * (0.5 if normalized else 0.5 / 255)
    np.testing.assert_allclose(transformed.normalize_intensity_payload(), expected)
    assert metadata.intensity_scale == 255


@pytest.mark.parametrize('normalized', (False, True))
def test_cellprofiler_registered_image_input_owner_enters_normalized_domain(normalized):
    from openhcs.core.artifacts import ArtifactSpec, ImageArtifactType
    from openhcs.interop.cellprofiler.runtime.output_recording import CellProfilerOutputRecorder

    raw = source(np.full((2, 3), 128, dtype=np.uint8))
    payload = raw.normalize_intensity_payload() if normalized else raw
    owner = CellProfilerOutputRecorder.for_artifact_type(ImageArtifactType)
    result = owner.runtime_input_value(ArtifactSpec.input('Input', ImageArtifactType), payload)
    np.testing.assert_allclose(result.data, 128 / 255)
    np.testing.assert_array_equal(result.mask, raw.mask)
    metadata = result.metadata
    assert metadata.has_normalized_intensity
    assert metadata.unit_interval_intensity_scale == 255
    assert metadata.source_image_names == ('Input',)
    assert metadata.without_unit_interval_intensity_scale().has_normalized_intensity
