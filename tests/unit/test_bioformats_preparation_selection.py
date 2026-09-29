"""Known physical-source selections reach discovery before container opens."""

import json
from pathlib import Path

import numpy as np
import pytest
import tifffile
from objectstate.lazy_factory import ensure_global_config_context
from polystore.bioformats_java import BioFormatsJavaContext

from openhcs.constants.constants import AllComponents, Microscope
from openhcs.core.config import (
    GlobalPipelineConfig,
    LazySourceBindingsConfig,
    PipelineConfig,
)
from openhcs.core.image_file_serialization import TiffImageFileFormat
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.source_bindings import (
    ImagePlaneSource,
    MetadataSelector,
    NamedSourceBinding,
    SourceBindingsConfig,
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
    SourceSelector,
)
from openhcs.microscopes.bioformats import BioFormatsHandler
from openhcs.microscopes.bioformats_adapter import BioFormatsJavaAdapter
from tests.unit.bioformats_fixture import bioformats_filemanager
from tests.unit.test_bioformats_java_adapter import (
    FakeBioFormatsContext,
    FakeBioFormatsMetadata,
)


def _file_filter(name):
    return SourceFilterClause(
        SourceFilterSubject.FILE, SourceFilterMatchType.EQUALS, name
    )


class _SelectionContext(FakeBioFormatsContext):
    """Controlled decoder response, preserving the real discovery/workspace path."""

    single_file = True

    def ensure_initialized(self):
        pass

    def ImageReader(self):
        return self

    def isSingleFile(self, path):
        return self.single_file

    def close(self):
        pass


@pytest.mark.parametrize("selection", ("global", "binding"))
@pytest.mark.parametrize("entrypoint", ("handler", "orchestrator", "auto_orchestrator"))
def test_selected_container_opens_once_and_projects_both_planes(
    tmp_path, monkeypatch, selection, entrypoint
):
    names = [f"container-{index:02}.czi" for index in range(16)]
    metadata = {}
    for index, name in enumerate(names):
        (tmp_path / name).touch()
        metadata[name] = FakeBioFormatsMetadata(
            well_column=index,
            well_id=f"Well:0:{index}",
            sample_id=f"WellSample:{index}",
            image_id=f"Image:{index}",
        )
    context = _SelectionContext(metadata, declared_suffixes=(".czi",))
    opened = []
    original_open = context.open_reader

    def counted_open(path):
        opened.append(Path(path).name)
        return original_open(path)

    monkeypatch.setattr(context, "open_reader", counted_open)
    monkeypatch.setattr(
        BioFormatsJavaContext, "instance", classmethod(lambda cls: context)
    )
    filters = (_file_filter(names[7]),)
    bindings = SourceBindingsConfig(
        source_filters=filters if selection == "global" else (),
        bindings=(
            NamedSourceBinding(
                alias="selected",
                selector=SourceSelector(
                    filters=filters if selection == "binding" else (),
                ),
            ),
        ),
    )
    filemanager = bioformats_filemanager()
    if entrypoint == "handler":
        handler = BioFormatsHandler(filemanager, source_bindings_config=bindings)
        assert handler.initialize_workspace(tmp_path, filemanager) == tmp_path
        assert opened == [names[7]]
    else:
        ensure_global_config_context(GlobalPipelineConfig, GlobalPipelineConfig())
        orchestrator = PipelineOrchestrator(
            tmp_path,
            storage_registry=filemanager.registry,
            pipeline_config=PipelineConfig(
                microscope=Microscope.AUTO
                if entrypoint == "auto_orchestrator"
                else Microscope.BIOFORMATS,
                source_bindings_config=LazySourceBindingsConfig(
                    source_filters=bindings.source_filters,
                    bindings=bindings.bindings,
                ),
            ),
        ).initialize()
        assert orchestrator.is_initialized()
        assert opened == [names[7]] * (2 if entrypoint == "auto_orchestrator" else 1)
        assert len(orchestrator.get_component_keys(AllComponents.WELL)) == 1
    workspace = json.loads((tmp_path / "openhcs_metadata.json").read_text())
    mapping = workspace["subdirectories"]["."]["workspace_mapping"]
    assert len(mapping) == 2
    assert all(names[7] in ref["backend_address"] for ref in mapping.values())


def test_real_tiff_orchestrator_only_decodes_selected_source(tmp_path, monkeypatch):
    names = [f"source-{index:02}.tif" for index in range(16)]
    for index, name in enumerate(names):
        tifffile.imwrite(tmp_path / name, np.full((8, 8), index, dtype=np.uint16))
    decoded = []
    original_read = TiffImageFileFormat.read

    def counted_read(self, path):
        decoded.append(Path(path).name)
        return original_read(self, path)

    monkeypatch.setattr(TiffImageFileFormat, "read", counted_read)
    ensure_global_config_context(GlobalPipelineConfig, GlobalPipelineConfig())
    filemanager = bioformats_filemanager()
    orchestrator = PipelineOrchestrator(
        tmp_path,
        storage_registry=filemanager.registry,
        pipeline_config=PipelineConfig(
            microscope=Microscope.AUTO,
            source_bindings_config=LazySourceBindingsConfig(
                bindings=(
                    NamedSourceBinding(
                        alias="selected",
                        selector=SourceSelector(filters=(_file_filter(names[7]),)),
                    ),
                ),
            ),
        ),
    ).initialize()
    assert orchestrator.is_initialized()
    assert decoded == [names[7], names[7]]
    workspace = json.loads((tmp_path / "openhcs_metadata.json").read_text())
    (reference,) = workspace["subdirectories"]["."]["workspace_mapping"].values()
    assert reference["backend_address"] == names[7]
    pixels = filemanager.load(str(tmp_path / reference["backend_address"]), "disk")
    np.testing.assert_array_equal(pixels, np.full((8, 8), 7, dtype=np.uint16))


def test_companion_path_selection_does_not_discard_its_container(tmp_path, monkeypatch):
    (tmp_path / "plate.fake").touch()
    context = _SelectionContext()
    context.single_file = False
    monkeypatch.setattr(
        BioFormatsJavaContext, "instance", classmethod(lambda cls: context)
    )
    config = SourceBindingsConfig(source_filters=(_file_filter("well-a01.tif"),))
    (dataset,) = BioFormatsJavaAdapter(config).discover_stores(tmp_path)
    assert len(dataset.candidates) == 2
    assert all(
        "well-a01.tif" in c.source_filter_path_identities() for c in dataset.candidates
    )


def test_global_companion_filter_is_applied_after_container_decode(tmp_path, monkeypatch):
    names = ("selected.fake", "unrelated.fake")
    metadata = {}
    for index, name in enumerate(names):
        (tmp_path / name).touch()
        metadata[name] = FakeBioFormatsMetadata(
            well_column=index,
            well_id=f"Well:0:{index}",
            sample_id=f"WellSample:{index}",
            image_id=f"Image:{index}",
        )
    context = _SelectionContext(metadata)
    context.single_file = False
    original_open = context.open_reader

    def with_companion(path):
        opened = original_open(path)
        opened.reader.used_files = (Path(path).name, f"{Path(path).stem}.tif")
        return opened

    monkeypatch.setattr(context, "open_reader", with_companion)
    monkeypatch.setattr(
        BioFormatsJavaContext, "instance", classmethod(lambda cls: context)
    )
    filemanager = bioformats_filemanager()
    handler = BioFormatsHandler(
        filemanager,
        source_bindings_config=SourceBindingsConfig(
            source_filters=(_file_filter("selected.tif"),)
        ),
    )
    handler.initialize_workspace(tmp_path, filemanager)
    workspace = json.loads((tmp_path / "openhcs_metadata.json").read_text())
    mapping = workspace["subdirectories"]["."]["workspace_mapping"]
    assert len(mapping) == 2
    assert all("selected.fake" in ref["backend_address"] for ref in mapping.values())


def test_binding_selection_is_union_and_metadata_is_not_guessed(tmp_path):
    bindings = SourceBindingsConfig(
        bindings=(
            NamedSourceBinding(
                alias="first", selector=SourceSelector(filters=(_file_filter("a.czi"),))
            ),
            NamedSourceBinding(
                alias="second",
                selector=SourceSelector(filters=(_file_filter("b.czi"),)),
            ),
        )
    )
    assert bindings.discovery_path_matches(tmp_path, tmp_path / "a.czi")
    assert bindings.discovery_path_matches(tmp_path, tmp_path / "b.czi")
    assert not bindings.discovery_path_matches(tmp_path, tmp_path / "c.czi")
    unrestricted = SourceBindingsConfig(
        bindings=(*bindings.bindings, NamedSourceBinding(alias="all"))
    )
    assert unrestricted.discovery_path_matches(tmp_path, tmp_path / "c.czi")


def test_explicit_source_and_metadata_only_discovery_stay_declared(tmp_path):
    selected = tmp_path / "selected.czi"
    selected.touch()
    exact = SourceBindingsConfig(
        bindings=(
            NamedSourceBinding(
                alias="exact", explicit_source=ImagePlaneSource(uri="selected.czi")
            ),
        )
    )
    assert exact.discovery_path_matches(tmp_path, selected)
    assert not exact.discovery_path_matches(tmp_path, tmp_path / "unrelated.czi")
    metadata_only = SourceBindingsConfig(
        bindings=(
            NamedSourceBinding(
                alias="decoded",
                selector=SourceSelector(metadata=(MetadataSelector("well", "A01"),)),
            ),
        )
    )
    # The filename cannot establish which decoded well this container supplies.
    assert metadata_only.discovery_path_matches(tmp_path, tmp_path / "unrelated.czi")


def test_discovery_reuses_directory_or_group_filter_semantics(tmp_path):
    filters = (
        SourceFilterClause(
            SourceFilterSubject.DIRECTORY, SourceFilterMatchType.CONTAINS, "selected"
        ),
        SourceFilterClause(
            SourceFilterSubject.FILE, SourceFilterMatchType.EQUALS, "a.czi", any_group=0
        ),
        SourceFilterClause(
            SourceFilterSubject.FILE, SourceFilterMatchType.EQUALS, "b.czi", any_group=0
        ),
    )
    config = SourceBindingsConfig(source_filters=filters)
    assert config.discovery_path_matches(tmp_path, tmp_path / "selected" / "a.czi")
    assert config.discovery_path_matches(tmp_path, tmp_path / "selected" / "b.czi")
    assert not config.discovery_path_matches(tmp_path, tmp_path / "selected" / "c.czi")
    assert not config.discovery_path_matches(tmp_path, tmp_path / "other" / "a.czi")
