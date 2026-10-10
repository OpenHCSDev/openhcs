"""Typed image sets retain physical coverage across volume/plane exports."""

from dataclasses import replace
import json
from pathlib import Path

import imageio.v3 as imageio
import numpy as np
import pytest
from polystore.virtual_workspace import SourcePixelRef

from benchmark.matched_cellprofiler_batch import _require_compared_output_inventory
from openhcs.core.artifacts import ImageArtifactType
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from benchmark.equivalence.comparison import runtime_image_differences
from benchmark.equivalence.images import RuntimeImageSnapshot
from benchmark.equivalence.outputs import RuntimeOutputSnapshot
from openhcs.core.equivalence.policy import RuntimeEquivalencePolicy
from openhcs.core.runtime_execution_validation import (
    RuntimeArtifactExecutionObservation,
)
from openhcs.core.runtime_exports import RuntimeExportObservation
from openhcs.core.runtime_image_values import ImageMaskDomain, ImagePayloadMetadata
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_matching import SourceImageSetIdentityPolicy
from openhcs.core.source_projection import (
    OpenHCSPlaneAddress,
    SourceArtifactProjection,
    SourceProjectionMetadataSerializer,
    SourceProjectionSet,
)
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.virtual_workspace_metadata import METADATA_CONFIG
from openhcs.core.dataset_sources.source_schema import SourceSchemaFilenameParser
from openhcs.domains.microscopy.axes import Microscopy
from openhcs.core.payload_axes import PayloadAxes

Z_STACK = SourceImageSetIdentityPolicy(frozenset({Microscopy.ZIndex}))
EXACT = RuntimeEquivalencePolicy(image_abs_tolerance=0, image_rel_tolerance=0)


def _write_metadata(root, projections):
    projections = tuple(projections)
    metadata = SourceProjectionMetadataSerializer(
        parser=SourceSchemaFilenameParser()
    ).metadata_dict(
        SourceProjectionSet(tuple(projections)),
        microscope_handler_name="source_bindings",
        source_filename_parser_name="SourceSchemaFilenameParser",
        grid_dimensions=[],
        pixel_size=1.0,
        projection_paths=tuple(
            (projection, f"virtual-{index}.tiff")
            for index, projection in enumerate(projections)
        ),
    )
    METADATA_CONFIG.metadata_path(root).write_text(
        json.dumps({"subdirectories": {".": metadata}})
    )


@pytest.fixture
def exported_volume(tmp_path):
    candidate = tmp_path / "candidate"
    native = tmp_path / "native"
    candidate.mkdir()
    native.mkdir()
    volume = np.arange(105, dtype=np.uint16).reshape(3, 5, 7)
    imageio.imwrite(native / "native-volume.tiff", volume)
    projections = []
    for plane_index, plane in enumerate(volume):
        path = candidate / f"opaque-{plane_index}.tiff"
        imageio.imwrite(path, plane)
        address = OpenHCSPlaneAddress(((Microscopy.Well, "A01"), (Microscopy.Site, "1"), (Microscopy.Channel, "2"), (Microscopy.ZIndex, plane_index + 1), (Microscopy.Timepoint, "1")))
        projections.append(
            SourceArtifactProjection(
                address=address,
                ref=SourcePixelRef("disk", path.name),
                source_alias="SavedImage",
                artifact_kind=ImageArtifactType,
                execution_scope=RuntimeExecutionAxisScope(axis_id="A01"),
                image_metadata=ImagePayloadMetadata(
                    source_component_metadata=address.as_component_metadata(),
                    source_dtype="uint16",
                    intensity_scale=65535.0,
                    source_spatial_domain=SourceSpatialDomain(
                        origin_yx=(0, 0), source_shape_yx=(5, 7)
                    ),
                ),
            )
        )
    _write_metadata(candidate, reversed(projections))
    return candidate, native, volume, projections


def _snapshot(root):
    return RuntimeOutputSnapshot.from_output_root(root, image_set_policy=Z_STACK)


def test_volume_plane_comparison_preserves_every_physical_file(exported_volume):
    candidate, native, volume, _ = exported_volume
    actual = _snapshot(candidate)
    reference = RuntimeOutputSnapshot.from_output_root(native)
    assert len(actual.images) == len(reference.images) == 1
    assert actual.images[0].dtype == "uint16"
    np.testing.assert_array_equal(actual.images[0].pixel_data, volume)
    assert actual.images[0].physical_paths == tuple(
        candidate / f"opaque-{i}.tiff" for i in range(3)
    )
    assert not runtime_image_differences(reference.images, actual.images, EXACT)
    exports = tuple(
        RuntimeExportObservation.from_output_root(root) for root in (native, candidate)
    )
    _require_compared_output_inventory(
        reference_files=frozenset(native.iterdir()),
        candidate_files=frozenset(candidate.iterdir()),
        reference_exports=exports[0],
        candidate_exports=exports[1],
        reference_snapshot=reference,
        candidate_snapshot=actual,
        candidate_managed_files=frozenset({METADATA_CONFIG.metadata_path(candidate)}),
    )


def test_2d_identity_does_not_infer_a_z_volume_from_coordinates(exported_volume):
    candidate, _, _, _ = exported_volume
    snapshot = RuntimeOutputSnapshot.from_output_root(candidate)
    assert len(snapshot.images) == 3
    assert all(
        image.shape == (5, 7) and len(image.physical_paths) == 1
        for image in snapshot.images
    )


def test_projection_owner_partitions_whole_exports_and_scalar_cohorts(exported_volume):
    _, _, _, projections = exported_volume
    whole_image = replace(
        projections[0],
        address=None,
        ref=SourcePixelRef("disk", "whole-volume.tiff"),
        image_metadata=ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE),
    )
    declared = SourceProjectionSet((whole_image, *reversed(projections)))
    whole, planes = declared.image_export_groups(Z_STACK)
    assert whole == (whole_image,)
    assert planes == (tuple(projections),)
    identity_images, identity_planes = declared.image_export_groups(
        SourceImageSetIdentityPolicy()
    )
    assert identity_images == declared.artifact_projections
    assert identity_planes == ()


def test_observation_owns_the_grouping_axis(exported_volume):
    candidate, _, volume, _ = exported_volume
    observation = RuntimeArtifactExecutionObservation(
        records_by_axis={},
        exports=RuntimeExportObservation.from_output_root(candidate),
        source_image_set_identity_policy=Z_STACK,
    )
    snapshot = RuntimeOutputSnapshot.from_artifact_execution_observation(
        observation, source_workspaces=(candidate,)
    )
    np.testing.assert_array_equal(snapshot.images[0].pixel_data, volume)


@pytest.mark.parametrize(
    "component",
    (
        Microscopy.Well,
        Microscopy.Site,
        Microscopy.Channel,
        Microscopy.Timepoint,
    ),
)
def test_different_source_cohorts_cannot_be_combined(exported_volume, component):
    candidate, _, _, projections = exported_volume
    changed_address = projections[1].address.with_value(
        component, "B02" if component is Microscopy.Well else "2"
    )
    if component is Microscopy.Channel:
        changed_address = projections[1].address.with_value(component, "3")
    projections[1] = replace(
        projections[1],
        address=changed_address,
        image_metadata=projections[1].image_metadata.replace_fields(
            source_component_metadata=changed_address.as_component_metadata()
        ),
    )
    _write_metadata(candidate, projections)
    with pytest.raises(ValueError, match="unique and contiguous"):
        _snapshot(candidate)


@pytest.mark.parametrize("change", ("producer", "execution_scope"))
def test_producer_and_execution_cohorts_remain_distinct(exported_volume, change):
    candidate, _, _, projections = exported_volume
    changes = (
        {"source_alias": "AnotherProducer"}
        if change == "producer"
        else {"execution_scope": RuntimeExecutionAxisScope(axis_id="B02")}
    )
    projections[1] = replace(projections[1], **changes)
    _write_metadata(candidate, projections)
    with pytest.raises(ValueError, match="unique and contiguous"):
        _snapshot(candidate)


@pytest.mark.parametrize(
    "metadata_changes, message",
    (
        ({"plane_axis": RuntimePlaneAxis.RUNTIME_SLICE}, "scalar image metadata"),
        ({"axes": PayloadAxes.colour_samples(0)}, "declared non-spatial axes"),
        ({"source_dtype": "uint8"}, "declared dtype"),
        ({"mask_defines_border": True}, "incompatible image metadata"),
        (
            {
                "source_spatial_domain": SourceSpatialDomain(
                    origin_yx=(1, 0), source_shape_yx=(5, 7)
                )
            },
            "crop exceeds",
        ),
    ),
)
def test_declared_axis_dtype_mask_and_geometry_conflicts_fail(
    exported_volume, metadata_changes, message
):
    candidate, _, _, projections = exported_volume
    projections[1] = replace(
        projections[1],
        image_metadata=projections[1].image_metadata.replace_fields(**metadata_changes),
    )
    _write_metadata(candidate, projections)
    with pytest.raises(ValueError, match=message):
        _snapshot(candidate)


def test_missing_plane_fails_contiguity(exported_volume):
    candidate, _, _, projections = exported_volume
    (candidate / projections[1].ref.backend_address).unlink()
    with pytest.raises(ValueError, match="unique and contiguous"):
        _snapshot(candidate)


def test_source_z_origin_is_preserved_without_assuming_one(exported_volume):
    candidate, _, volume, projections = exported_volume
    shifted = []
    for index, projection in enumerate(projections):
        address = projection.address.with_value(Microscopy.ZIndex, str(index + 7))
        shifted.append(
            replace(
                projection,
                address=address,
                image_metadata=projection.image_metadata.replace_fields(
                    source_component_metadata=address.as_component_metadata()
                ),
            )
        )
    _write_metadata(candidate, reversed(shifted))
    np.testing.assert_array_equal(_snapshot(candidate).images[0].pixel_data, volume)


@pytest.mark.parametrize("change", ("producer", "execution_scope"))
def test_split_contiguous_cohort_still_fails_logical_cardinality(
    exported_volume, change
):
    candidate, native, _, projections = exported_volume
    changes = (
        {"source_alias": "AnotherProducer"}
        if change == "producer"
        else {"execution_scope": RuntimeExecutionAxisScope(axis_id="B02")}
    )
    projections[-1] = replace(projections[-1], **changes)
    _write_metadata(candidate, projections)
    reference = RuntimeOutputSnapshot.from_output_root(native)
    actual = _snapshot(candidate)
    assert len(actual.images) == 2
    assert runtime_image_differences(reference.images, actual.images, EXACT)


def test_missing_last_plane_fails_pixel_shape_comparison(exported_volume):
    candidate, native, _, projections = exported_volume
    (candidate / projections[-1].ref.backend_address).unlink()
    reference = RuntimeOutputSnapshot.from_output_root(native)
    assert runtime_image_differences(
        reference.images, _snapshot(candidate).images, EXACT
    )


def test_declared_plane_domain_rejects_a_missing_tail(exported_volume):
    candidate, _, _, projections = exported_volume
    indexed = []
    for index, projection in enumerate(projections):
        indexed.append(
            replace(
                projection,
                image_metadata=projection.image_metadata.replace_fields(
                    source_component_metadata={
                        **dict(projection.image_metadata.source_component_metadata),
                        "source_plane_index": str(index),
                        "source_plane_count": str(len(projections)),
                    }
                ),
            )
        )
    _write_metadata(candidate, indexed)
    (candidate / projections[-1].ref.backend_address).unlink()
    with pytest.raises(ValueError, match="Declared source-plane count conflicts"):
        _snapshot(candidate)


def test_unindexed_image_is_not_hidden_by_logical_grouping(exported_volume):
    candidate, _, _, _ = exported_volume
    imageio.imwrite(candidate / "unexpected.tiff", np.zeros((5, 7), np.uint16))
    with pytest.raises(ValueError, match="every physical image file exactly once"):
        _snapshot(candidate)


def test_one_physical_file_cannot_belong_to_two_logical_images(exported_volume):
    candidate, _, _, projections = exported_volume
    another = [replace(p, source_alias="AnotherProducer") for p in projections]
    _write_metadata(candidate, projections + another)
    with pytest.raises(ValueError, match="duplicate path|exactly once"):
        _snapshot(candidate)


def test_duplicate_z_rejected_by_existing_projection_owner(exported_volume):
    _, _, _, projections = exported_volume
    with pytest.raises(ValueError, match="Duplicate source projection address"):
        SourceProjectionSet(
            (projections[0], replace(projections[1], address=projections[0].address))
        )


def test_source_axis_projection_cannot_turn_a_plane_into_a_row(exported_volume):
    candidate, _, _, projections = exported_volume
    projections[1] = replace(
        projections[1],
        ref=SourcePixelRef("disk", projections[1].ref.backend_address, (0,)),
    )
    _write_metadata(candidate, projections)
    with pytest.raises(ValueError, match="two spatial pixel axes"):
        _snapshot(candidate)


def test_changed_pixels_and_missing_logical_image_fail_comparison(exported_volume):
    candidate, native, volume, _ = exported_volume
    changed = volume[1].copy()
    changed[0, 0] += 1
    imageio.imwrite(candidate / "opaque-1.tiff", changed)
    reference = RuntimeOutputSnapshot.from_output_root(native)
    assert runtime_image_differences(
        reference.images, _snapshot(candidate).images, EXACT
    )
    assert runtime_image_differences(reference.images, (), EXACT)


def test_physical_path_owner_rejects_empty_and_duplicate_paths():
    image = RuntimeImageSnapshot.from_array("one.tiff", np.zeros((5, 7), np.uint16))
    for paths in ((), (image.path, image.path)):
        with pytest.raises(ValueError, match="nonempty unique physical paths"):
            replace(image, physical_paths=paths)


def test_channel_slice_precedes_invalid_declared_axis_and_uses_modulo():
    events = []

    class FailingPixels:
        shape = (2, 5, 7)

        def __getitem__(self, key):
            events.append(key)
            raise RuntimeError("pixel slice failure")

    pixels = FailingPixels()
    metadata = ImagePayloadMetadata(axes=PayloadAxes.colour_samples(99))
    with pytest.raises(RuntimeError, match="pixel slice failure"):
        metadata.project_channel_payload(pixels, pixels, 1, channel_axis=9)
    assert events == [(slice(1, 2), slice(None), slice(None))]
    with pytest.raises(ValueError, match="axis at position 99 is invalid"):
        metadata.project_channel_payload(
            pixels, pixels, 1, channel_data=np.zeros((1, 5, 7)), channel_axis=9
        )
    assert len(events) == 1


def test_channel_projection_preserves_shared_masks_and_squeezed_views():
    pixels = np.arange(70).reshape(2, 5, 7)
    shared_mask = np.ones((5, 7), dtype=bool)
    selected = ImageMaskDomain.channel_axis_slice(
        pixels, channel_axis=-3, channel_index=1
    )
    assert np.shares_memory(selected, pixels)
    unchanged = ImageMaskDomain.projected_channel_mask(
        shared_mask,
        source_data=pixels,
        channel_data=selected,
        channel_index=1,
        channel_axis=-3,
    )
    assert unchanged is shared_mask
    full_mask = pixels % 3 == 0
    squeezed = ImageMaskDomain.projected_channel_mask(
        full_mask,
        source_data=pixels,
        channel_data=selected[0],
        channel_index=1,
        channel_axis=-3,
    )
    np.testing.assert_array_equal(squeezed, full_mask[1])
    assert np.shares_memory(squeezed, full_mask)


def test_mask_conversion_failure_precedes_source_geometry():
    class BadMask:
        def __array__(self, dtype=None, copy=None):
            raise RuntimeError("mask conversion failure")

    class BadPixels:
        @property
        def shape(self):
            raise AssertionError("source geometry must not run first")

    with pytest.raises(RuntimeError, match="mask conversion failure"):
        ImageMaskDomain.projected_channel_mask(
            BadMask(),
            source_data=BadPixels(),
            channel_data=np.zeros((5, 7)),
            channel_index=0,
            channel_axis=0,
        )
