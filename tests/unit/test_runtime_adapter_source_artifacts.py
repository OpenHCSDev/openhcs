from openhcs.core.steps.abstract import StepExecutionObservation
from pathlib import Path
from types import SimpleNamespace

import numpy as np
import pytest
from polystore.base import ensure_storage_registry, storage_registry
from polystore.filemanager import FileManager
from scipy.io import savemat

from openhcs.constants.constants import Backend
from openhcs.constants.input_source import InputSource
from openhcs.core.artifacts import ImageArtifactType, ObjectLabelsArtifactType
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.runtime_adapters import RuntimeAdapterRequest
from openhcs.core.runtime_image_loading import ImagePayloadSourceMetadataContext
from openhcs.core.runtime_image_values import image_payload_data, image_payload_metadata
from openhcs.core.runtime_source_binding_cache import RuntimeSourceBindingContextCache
from openhcs.core.source_binding_selection import SourcePatternResolutionContext
from openhcs.core.runtime_object_labels import ObjectLabelSet
from openhcs.core.source_binding_workspace import SourceBindingWorkspaceProjector
from openhcs.core.source_bindings import (
    CompiledSourceBindingPlan,
    NamedSourceBinding,
    SourceBindingMatchMethod,
    SourceBindingMatchPlan,
    SourceBindingsConfig,
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
    SourceProjectionRole,
    SourceSelector,
    StepSourceBindingsConfig,
)
from openhcs.core.source_image_provenance import SourceImageIdentity
from openhcs.core.source_matching import SourceImageSetIdentityPolicy
from openhcs.core.source_projection import SourcePlaneProjection
from openhcs.core.source_workspace_projection import (
    VirtualWorkspacePathLookup,
    VirtualWorkspaceSourceProjectionAuthority,
    VirtualWorkspaceSourceProjectionCache,
)
from openhcs.interop.cellprofiler.runtime.output_recording import (
    CellProfilerOutputRecorder,
)
from openhcs.core.dataset_sources.choice import DatasetSourceChoice
from openhcs.core.dataset_sources.openhcs_format import OpenHCSDatasetSource
from openhcs.core.dataset_sources.source_schema import SourceSchemaFilenameParser
from openhcs.domains.microscopy.axes import Microscopy


def _filemanager() -> FileManager:
    ensure_storage_registry()
    return FileManager(dict(storage_registry))


def test_source_artifact_inputs_share_workspace_vfs_and_contract_resolution(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source_root = tmp_path / "source"
    workspace_root = tmp_path / "workspace"
    source_root.mkdir()
    primary_path = source_root / "primary.npy"
    illumination_path = source_root / "illumination.mat"
    labels_path = source_root / "labels.npy"
    primary = np.arange(20, dtype=np.uint16).reshape(4, 5)
    illumination = np.full((4, 5), 0.25, dtype=np.float32)
    labels = np.array(
        [[0, 1, 1, 0, 0], [0, 1, 1, 0, 2], [0, 0, 0, 0, 2], [3, 3, 0, 0, 0]],
        dtype=np.uint16,
    )
    np.save(primary_path, primary)
    savemat(illumination_path, {"Image": illumination})
    np.save(labels_path, labels)

    def binding(
        alias: str,
        source_path: Path,
        *,
        artifact_kind=ImageArtifactType,
        projection_role=SourceProjectionRole.PRIMARY_PLANE,
    ) -> NamedSourceBinding:
        return NamedSourceBinding(
            alias=alias,
            artifact_kind=artifact_kind,
            projection_role=projection_role,
            selector=SourceSelector(
                filters=(
                    SourceFilterClause(
                        SourceFilterSubject.FILE,
                        SourceFilterMatchType.EQUALS,
                        source_path.name,
                    ),
                )
            ),
        )

    primary_binding = binding("Primary", primary_path)
    illumination_binding = binding(
        "Illumination",
        illumination_path,
        projection_role=SourceProjectionRole.SOURCE_ARTIFACT,
    )
    labels_binding = binding(
        "Labels",
        labels_path,
        artifact_kind=ObjectLabelsArtifactType,
        projection_role=SourceProjectionRole.SOURCE_ARTIFACT,
    )
    source_bindings = SourceBindingsConfig(
        bindings=(
            primary_binding,
            illumination_binding,
            labels_binding,
        ),
        match_plan=SourceBindingMatchPlan(SourceBindingMatchMethod.ORDER),
    )
    filemanager = _filemanager()
    SourceBindingWorkspaceProjector(
        source_bindings,
        parser=SourceSchemaFilenameParser(),
    ).materialize(
        source_root,
        workspace_root,
        filemanager=filemanager,
        source_backend=Backend.DISK,
        workspace_backend=Backend.DISK,
        source_files=(primary_path, illumination_path, labels_path),
    )
    # This opens the persisted projection; it does not ingest workspace files
    # as a new raw source folder. Physical inputs remain in source_root.
    microscope_handler = DatasetSourceChoice.named("auto").open(workspace_root, filemanager=filemanager, source_bindings_config=source_bindings)
    assert isinstance(microscope_handler, OpenHCSDatasetSource)
    microscope_handler.initialize_workspace(workspace_root, filemanager)
    projection_cache = VirtualWorkspaceSourceProjectionCache()
    context = SimpleNamespace(
        completed_step_outputs=StepExecutionObservation.empty(),
        plate_path=workspace_root,
        filemanager=filemanager,
        microscope_handler=microscope_handler,
        runtime_source_binding_context_cache=RuntimeSourceBindingContextCache(),
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(
            frozenset((Microscopy.Channel,))
        ),
    )
    context.runtime_source_workspace_projection_authority = VirtualWorkspaceSourceProjectionAuthority.from_context(
        context, cache=projection_cache,
    )
    projection = VirtualWorkspaceSourceProjectionAuthority.from_context(
        context,
        cache=projection_cache,
    ).projection_or_empty()
    primary_virtual_path = next(
        virtual_path
        for virtual_path in projection.pipeline_start_files(axis_id="A01")
        if isinstance(
            projection.require_source_projection_for(
                VirtualWorkspacePathLookup.from_paths(
                    virtual_path,
                    virtual_path,
                )
            ),
            SourcePlaneProjection,
        )
    )
    primary_lookup = VirtualWorkspacePathLookup.from_paths(
        primary_virtual_path,
        primary_virtual_path,
    )
    primary_projection = projection.require_source_projection_for(primary_lookup)
    primary_payload = projection.project_payload(
        primary_lookup,
        filemanager.load(
            primary_virtual_path,
            Backend.VIRTUAL_WORKSPACE.value,
        ),
    )
    primary_payload = primary_binding.apply_loaded_payload(
        primary_payload,
        ImagePayloadSourceMetadataContext(
            SourceImageIdentity(
                primary_virtual_path,
                projection.source_metadata_for(primary_lookup),
            ),
            primary_projection.ref.backend,
            filemanager,
            primary_projection.ref.backend_address,
        ),
    )

    def request() -> RuntimeAdapterRequest:
        return RuntimeAdapterRequest(
            context=context,
            source_payload=primary_payload,
            source_binding_plan=CompiledSourceBindingPlan.from_config(
                StepSourceBindingsConfig(
                    bindings=source_bindings.binding_declarations,
                    match_plan=source_bindings.match_plan,
                    enabled=True,
                ),
            ),
            axis_scope=RuntimeExecutionAxisScope.from_raw(
                "A01",
                component=None,
                value=None,
            ),
        )

    illumination_request = request()
    illumination_payload = illumination_request.source_artifact_payload(
        illumination_binding.input_spec().ref()
    )
    np.testing.assert_array_equal(
        image_payload_data(illumination_payload),
        illumination[np.newaxis, ...],
    )

    primary_auxiliary_request = request()
    assert (
        primary_auxiliary_request.source_binding_for_artifact_ref(
            primary_binding.input_spec().ref()
        )
        == primary_binding
    )

    labels_request = request()
    labels_spec = labels_binding.input_spec()
    labels_payload = labels_request.source_artifact_payload(labels_spec.ref())
    label_set = CellProfilerOutputRecorder.for_artifact_type(
        ObjectLabelsArtifactType
    ).raw_runtime_input_value(
        spec=labels_spec, value=labels_payload
    )
    assert isinstance(label_set, ObjectLabelSet)
    np.testing.assert_array_equal(label_set.labels, labels[np.newaxis, ...])

    # Exercise the actual source adapter and VFS under the independent live
    # selector route. Payload identity belongs to the unchanged typed source
    # projection, not the selector's resolved metadata record representation.
    with monkeypatch.context() as live_selector:
        live_selector.setattr(
            RuntimeSourceBindingContextCache,
            "source_pattern_context",
            lambda self, **kwargs: SourcePatternResolutionContext.from_projection(
                **kwargs
            ),
        )
        live_illumination = request().source_artifact_payload(
            illumination_binding.input_spec().ref()
        )
        live_labels = request().source_artifact_payload(labels_spec.ref())
    for produced, live in (
        (illumination_payload, live_illumination),
        (labels_payload, live_labels),
    ):
        np.testing.assert_array_equal(
            image_payload_data(produced), image_payload_data(live)
        )
        produced_metadata = image_payload_metadata(produced)
        live_metadata = image_payload_metadata(live)
        assert produced_metadata == live_metadata
        assert (
            produced_metadata.source_provenance.source_identity.identity
            == live_metadata.source_provenance.source_identity.identity
        )
        assert (
            produced_metadata.source_provenance.represented_source_identities
            == live_metadata.source_provenance.represented_source_identities
        )


@pytest.mark.parametrize("mode", ("rgb", "monochrome", "mask"))
def test_workspace_materialization_preserves_declared_source_pixels(tmp_path, mode):
    from PIL import Image
    from skimage.color import rgb2gray
    source_root, workspace_root = tmp_path / "source", tmp_path / "workspace"
    source_root.mkdir()
    path = source_root / "A01_s1_w1_z001_t001.tif"
    pixels = np.arange(60, dtype=np.uint8).reshape(4, 5, 3)
    if mode == "mask":
        pixels = pixels[..., 0]
    Image.fromarray(pixels).save(path)
    binding = NamedSourceBinding(
        alias="Raw", load_as_monochrome=mode == "monochrome", load_as_mask=mode == "mask",
    )
    bindings = SourceBindingsConfig(bindings=(binding,))
    filemanager = _filemanager()
    SourceBindingWorkspaceProjector(bindings, parser=SourceSchemaFilenameParser()).materialize(
        source_root, workspace_root, filemanager=filemanager,
        source_backend=Backend.DISK, workspace_backend=Backend.DISK, source_files=(path,),
    )
    microscope = DatasetSourceChoice.named("auto").open(workspace_root, filemanager=filemanager, source_bindings_config=bindings)
    microscope.initialize_workspace(workspace_root, filemanager)
    cache = VirtualWorkspaceSourceProjectionCache()
    context = SimpleNamespace(
        completed_step_outputs=StepExecutionObservation.empty(),
        plate_path=workspace_root, filemanager=filemanager, microscope_handler=microscope,
    )
    workspace = VirtualWorkspaceSourceProjectionAuthority.from_context(context, cache=cache).projection_or_empty()
    paths = tuple(path for path, _projection in workspace.source_occurrences_for_binding(binding, axis_id="A01"))
    assert len(paths) == 1
    (payload,) = workspace.load_binding_payloads(paths, binding=binding, filemanager=filemanager)
    expected = rgb2gray(pixels.astype(np.float32) / 255) if mode == "monochrome" else pixels.astype(bool) if mode == "mask" else pixels
    assert np.allclose(image_payload_data(payload), expected)
    metadata = image_payload_metadata(payload)
    assert metadata.source_channel_axis == (-1 if mode == "rgb" else None)
    assert metadata.source_provenance.represented_source_image_names == ("Raw",)
    if mode in ("monochrome", "mask"):
        assert metadata.has_normalized_intensity
