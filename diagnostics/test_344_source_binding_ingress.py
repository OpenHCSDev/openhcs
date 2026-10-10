"""Pure path/declaration reproducer: no pixels, workspace writes or native calls."""

from dataclasses import replace
from pathlib import Path

import pytest
from polystore.base import _create_storage_registry
from polystore.filemanager import FileManager

from openhcs.constants import AllComponents, Backend
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.core.source_binding_workspace import SourceBindingWorkspaceProjector, SourceSetAssembler
from openhcs.core.source_bindings import (
    MetadataExtractionRule, MetadataSource, source_bindings_defaults_to_base,
)
from openhcs.core.source_projection import OpenHCSPlaneAddress, SourceProjectionSet
from openhcs.core.dataset_sources.source_bindings_source import SourceBindingsSource
from openhcs.microscopes.imagexpress import ImageXpressHandler


EXAMPLE = (
    Path(__file__).resolve().parents[1]
    / "docs/refactor/examples/344-aligned-rescale-engineering.py"
)
ROOT = Path("/synthetic/engineering-fixture")
PATHS = tuple(
    ROOT / f"TimePoint_1/ZStep_{z}/A01_s{site:03}_w{channel}_z{z:03}_t001.tif"
    for z in (1, 2) for site in (1, 2) for channel in (1, 2)
)


def _config():
    document = PipelineDocumentCodec.from_source(EXAMPLE.read_text())
    assert document.pipeline_config.dataset_source is ImageXpressHandler
    return source_bindings_defaults_to_base(document.pipeline_config.source_bindings_config)


def test_explicit_imagexpress_with_bindings_is_routed_to_generic_ingestion():
    # Factory construction only. No initialize_workspace, I/O or compile.
    handler = ImageXpressHandler.open(
        ROOT,
        filemanager=FileManager(_create_storage_registry()),
        source_bindings_config=_config(),
    )
    assert isinstance(handler, SourceBindingsSource)


def test_metadata_empty_candidates_reproduce_exact_order_guard():
    config = replace(_config(), metadata_rules=(), match_plan=None)
    projector = SourceBindingWorkspaceProjector(config)
    candidates = projector.source_candidates(ROOT, PATHS, source_backend=Backend.DISK)
    selected = projector._candidates_by_alias(ROOT, candidates, filemanager=None)
    refs = tuple(tuple(item.source_ref for item in values) for values in selected.values())
    assert len(refs) == 2 and refs[0] == refs[1] and len(refs[0]) == 8
    with pytest.raises(ValueError, match="ORDER source bindings must distinguish aliases"):
        SourceSetAssembler.for_config(config).source_sets(None, selected, ())


def test_declared_acquisition_metadata_distinguishes_channels_site_and_z():
    config = _config()
    projector = SourceBindingWorkspaceProjector(config)
    candidates = projector.source_candidates(ROOT, PATHS, source_backend=Backend.DISK)
    assert len(candidates) == 8
    selected = projector._candidates_by_alias(ROOT, candidates, filemanager=None)
    assert tuple(selected) == ("EngineeringCH1", "EngineeringCH2")
    assert tuple(len(values) for values in selected.values()) == (2, 2)
    for channel, alias in enumerate(selected, start=1):
        members = selected[alias]
        assert tuple(member.metadata["z_index"] for member in members) == ("1", "2")
        assert all(member.metadata["well"] == "A01" for member in members)
        assert all(member.metadata["site"] == "1" for member in members)
        assert all(member.metadata["timepoint"] == "1" for member in members)
        assert all(member.metadata["channel"] == str(channel) for member in members)
        assert tuple(member.source_ref.backend_address for member in members) == tuple(
            f"TimePoint_1/ZStep_{z}/A01_s001_w{channel}_z{z:03}_t001.tif" for z in (1, 2)
        )
    sets = SourceSetAssembler.for_config(config).source_sets(config.match_plan, selected, ())
    assert len(sets) == 2
    for source_set in sets:
        members = tuple(source_set.candidates_by_alias.values())
        assert members[0].source_ref != members[1].source_ref
        assert members[0].metadata["z_index"] == members[1].metadata["z_index"]


def test_declared_folder_and_filename_z_conflicts_remain_rejected():
    config = _config()
    # The shipped recipe declares filename identity; this extra rule is a conflict
    # control of the existing extractor, not an extra required fixture declaration.
    config = replace(config, metadata_rules=(*config.metadata_rules, MetadataExtractionRule(
        MetadataSource.FOLDER_NAME,
        r"(?:^|/)ZStep_0*(?P<z_index>[1-9][0-9]*)$",
    )))
    projector = SourceBindingWorkspaceProjector(config)
    mismatched = ROOT / "TimePoint_1/ZStep_2/A01_s001_w1_z001_t001.tif"
    with pytest.raises(RuntimeError, match="Conflicting metadata field 'z_index'"):
        projector.source_candidates(ROOT, (mismatched,), source_backend=Backend.DISK)


def test_store_singleton_addresses_need_declared_component_identity():
    config = _config()
    projector = SourceBindingWorkspaceProjector(config)
    candidates = projector.source_candidates(ROOT, PATHS, source_backend=Backend.DISK)
    # This reproduces the parent's stated store-plane boundary without reading TIFFs.
    singleton = OpenHCSPlaneAddress.from_values(
        well="A01", site="1", channel="1", z_index="1", timepoint="1",
    )
    candidates = tuple(replace(item, declared_address=singleton) for item in candidates)
    metadata_only = replace(config, bindings=tuple(
        replace(binding, component_identity=()) for binding in config.bindings
    ))
    old_projector = SourceBindingWorkspaceProjector(metadata_only)
    old_selected = old_projector._candidates_by_alias(ROOT, candidates, filemanager=None)
    old_sets = SourceSetAssembler.for_config(metadata_only).source_sets(
        metadata_only.match_plan, old_selected, (),
    )
    with pytest.raises(ValueError, match="Duplicate source projection address"):
        SourceProjectionSet(old_projector._source_set_projections(metadata_only.bindings, old_sets))

    selected = projector._candidates_by_alias(ROOT, candidates, filemanager=None)
    sets = SourceSetAssembler.for_config(config).source_sets(config.match_plan, selected, ())
    projections = SourceProjectionSet(projector._source_set_projections(config.bindings, sets))
    assert len(projections.projections) == 4
    assert tuple((
        projection.address.value_for(AllComponents.WELL),
        projection.address.value_for(AllComponents.SITE),
        projection.address.value_for(AllComponents.CHANNEL),
        projection.address.value_for(AllComponents.Z_INDEX),
        projection.address.value_for(AllComponents.TIMEPOINT),
    ) for projection in projections.projections) == (
        ("A01", "1", "1", "1", "1"), ("A01", "1", "2", "1", "1"),
        ("A01", "1", "1", "2", "1"), ("A01", "1", "2", "2", "1"),
    )
    assert {projection.ref for projection in projections.projections} == {
        item.source_ref for members in selected.values() for item in members
    }
