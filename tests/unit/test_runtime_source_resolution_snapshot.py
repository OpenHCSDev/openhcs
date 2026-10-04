"""Resolution lifetimes across generic source selectors and artifact adapters."""

import pickle
from types import MappingProxyType

import pytest
from polystore.virtual_workspace import SourcePixelRef

from openhcs.constants.constants import AllComponents
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.runtime_source_binding_cache import RuntimeSourceBindingContextCache
from openhcs.core.source_binding_selection import (
    DeclaredSourceMetadataRecord,
    SourceBindingMatchedImageSet,
    SourcePatternResolutionContext,
)
from openhcs.core.source_bindings import (
    MetadataExtractionRule,
    MetadataSource,
)
from openhcs.core.source_matching import SourceImageSetIdentityPolicy
from openhcs.core.source_metadata import (
    ORIGINAL_SOURCE_METADATA_FIELD,
    ResolvedSourceMetadataRecord,
)
from openhcs.core.source_projection import OpenHCSPlaneAddress, SourcePlaneProjection
from openhcs.core.source_workspace_projection import VirtualWorkspaceSourceProjection
from openhcs.microscopes.microscope_interfaces import FilenameParseResult
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser

PATH = "A01_s001_w1_z001_t001.tif"


class CountingParser(SourceSchemaFilenameParser):
    def __init__(self):
        super().__init__()
        self.calls = []

    def parse_filename(self, path):
        self.calls.append(path)
        result = super().parse_filename(path)
        if result is None or self.pattern_format is None:
            return result
        return FilenameParseResult(
            tuple(
                (
                    component,
                    (
                        int(self.pattern_format)
                        if component is AllComponents.SITE
                        else value
                    ),
                )
                for component, value in result.declared_values()
            ),
            extension=result.extension,
        )


def projection(metadata):
    return VirtualWorkspaceSourceProjection(
        source_refs_by_virtual_path={PATH: SourcePixelRef("disk", "/source/image.tif")},
        source_metadata_by_path={PATH: metadata},
    )


def snapshot(cache, source_projection, parser, rules=()):
    return cache.source_pattern_context(
        parser=parser, projection=source_projection, metadata_rules=rules
    )


def test_declared_record_resolves_live_parser_and_nested_metadata():
    nested = {"Plate": "before"}
    record = DeclaredSourceMetadataRecord.from_mapping(
        {ORIGINAL_SOURCE_METADATA_FIELD: nested, "site": 8}
    )
    assert isinstance(record, DeclaredSourceMetadataRecord)
    parser = CountingParser()
    first = record.resolve(PATH, parser, ())
    nested["Plate"] = "after"
    second = record.resolve(PATH, parser, ())
    assert first["site"] == second["site"] == 8
    assert first[ORIGINAL_SOURCE_METADATA_FIELD]["Plate"] == "before"
    assert second[ORIGINAL_SOURCE_METADATA_FIELD]["Plate"] == "after"
    assert parser.calls == [PATH, PATH]


def test_runtime_snapshot_owns_nested_metadata_and_unknown_fallback():
    nested = {"Plate": "before"}
    source_projection = projection({ORIGINAL_SOURCE_METADATA_FIELD: nested})
    parser = CountingParser()
    cache = RuntimeSourceBindingContextCache()
    context = snapshot(cache, source_projection, parser)
    calls = tuple(parser.calls)
    nested["Plate"] = "after"
    for _ in range(3):
        metadata = context.metadata_for_path(PATH)
        assert isinstance(metadata, ResolvedSourceMetadataRecord)
        assert metadata[ORIGINAL_SOURCE_METADATA_FIELD]["Plate"] == "before"
    assert tuple(parser.calls) == calls
    with pytest.raises(TypeError):
        metadata[ORIGINAL_SOURCE_METADATA_FIELD]["Plate"] = "invalid"
    unknown = "A02_s001_w1_z001_t001.tif"
    assert context.metadata_for_path(unknown)["well"] == "A02"
    assert parser.calls[-1] == unknown
    assert snapshot(cache, source_projection, parser) is context
    entry = next(iter(cache.source_resolution_snapshots.values()))
    assert entry.projection is source_projection
    assert entry.context.parser is parser


def test_direct_projection_context_remains_live():
    nested = {"Plate": "before"}
    parser = CountingParser()
    context = SourcePatternResolutionContext.from_projection(
        parser=parser,
        projection=projection({ORIGINAL_SOURCE_METADATA_FIELD: nested}),
    )
    assert (
        context.metadata_for_path(PATH)[ORIGINAL_SOURCE_METADATA_FIELD]["Plate"]
        == "before"
    )
    nested["Plate"] = "after"
    assert (
        context.metadata_for_path(PATH)[ORIGINAL_SOURCE_METADATA_FIELD]["Plate"]
        == "after"
    )
    assert parser.calls == [PATH, PATH]


def test_snapshot_replacement_tracks_projection_parser_semantics_and_rules():
    cache = RuntimeSourceBindingContextCache()
    parser = CountingParser()
    source_projection = projection({})
    original = snapshot(cache, source_projection, parser)
    parser.pattern_format = "9"
    changed_parser = snapshot(cache, source_projection, parser)
    assert changed_parser is not original
    assert original.metadata_for_path(PATH)["site"] == 1
    assert changed_parser.metadata_for_path(PATH)["site"] == 9
    replaced_projection = snapshot(cache, projection({"site": 7}), parser)
    assert replaced_projection.metadata_for_path(PATH)["site"] == 7
    replaced_parser = snapshot(cache, source_projection, CountingParser())
    assert replaced_parser is not original
    assert replaced_parser.metadata_for_path(PATH)["site"] == 1
    rules = (
        MetadataExtractionRule(
            source=MetadataSource.FILE_NAME, pattern=r"(?P<Plate>A01)"
        ),
    )
    changed_rules = snapshot(cache, source_projection, parser, rules)
    assert changed_rules is not changed_parser
    assert (
        changed_rules.metadata_for_path(PATH)[ORIGINAL_SOURCE_METADATA_FIELD]["Plate"]
        == "A01"
    )


def test_matched_set_preserves_resolved_record_behavior_and_precedence():
    parser = CountingParser()
    context = snapshot(
        RuntimeSourceBindingContextCache(), projection({"site": None}), parser
    )
    matched = SourceBindingMatchedImageSet.from_plan(
        bindings=(),
        match_plan=None,
        source_context=context,
        identity_policy=SourceImageSetIdentityPolicy(),
    )
    calls = tuple(parser.calls)
    assert (
        matched.source_metadata_by_path[PATH] is context.source_metadata_by_path[PATH]
    )
    assert matched.metadata_for_path(PATH)["site"] == 1
    assert tuple(parser.calls) == calls


def test_virtual_positions_remain_distinct_with_shared_physical_address():
    other = "A01_s002_w1_z001_t001.tif"
    source_projection = VirtualWorkspaceSourceProjection(
        source_refs_by_virtual_path={
            PATH: SourcePixelRef("disk", "/source/shared.tif"),
            other: SourcePixelRef("disk", "/source/shared.tif"),
        },
        source_metadata_by_path=MappingProxyType(
            {PATH: {"site": 1}, other: {"site": 2}}
        ),
    )
    context = snapshot(
        RuntimeSourceBindingContextCache(), source_projection, CountingParser()
    )
    assert context.virtual_paths_for_source("/source/shared.tif") == (PATH, other)
    assert context.metadata_for_path(PATH)["site"] == 1
    assert context.metadata_for_path(other)["site"] == 2


def test_known_empty_record_remains_none_without_repeated_parsing():
    parser = CountingParser()
    source_projection = VirtualWorkspaceSourceProjection(
        source_refs_by_virtual_path={"opaque": SourcePixelRef("disk", "opaque")},
        source_metadata_by_path={},
    )
    context = snapshot(RuntimeSourceBindingContextCache(), source_projection, parser)
    calls = tuple(parser.calls)
    assert context.metadata_for_path("opaque") is None
    assert context.metadata_for_path("opaque") is None
    assert tuple(parser.calls) == calls


def test_snapshot_rejects_nested_values_outside_existing_metadata_grammar():
    with pytest.raises(TypeError, match="Source metadata scalar values"):
        snapshot(
            RuntimeSourceBindingContextCache(),
            projection({"nested": {"unsupported": {"deep": 1}}}),
            CountingParser(),
        )


def test_declared_and_resolved_records_preserve_family_value_identity():
    declared = DeclaredSourceMetadataRecord.from_mapping({"site": 1, "well": "A01"})
    resolved = ResolvedSourceMetadataRecord.from_mapping({"site": 1, "well": "A01"})
    assert declared == resolved
    assert hash(declared) == hash(resolved)
    assert hash(declared) == hash((declared.fields,))
    assert declared != DeclaredSourceMetadataRecord.from_mapping(
        {"site": 2, "well": "A01"}
    )
    nested = {ORIGINAL_SOURCE_METADATA_FIELD: {"Plate": "A"}}
    with pytest.raises(TypeError):
        hash(DeclaredSourceMetadataRecord.from_mapping(nested))
    with pytest.raises(TypeError):
        hash(ResolvedSourceMetadataRecord.from_mapping(nested))


def test_snapshot_owns_position_and_projection_map_views():
    original_ref = SourcePixelRef("disk", "/source/original.tif")
    refs = {PATH: original_ref}
    positions = {
        PATH: SourcePlaneProjection(
            address=OpenHCSPlaneAddress.from_values("A01", 1, 1, 1, 1),
            ref=original_ref,
            source_alias="original",
        )
    }
    original_projection = positions[PATH]
    source_projection = VirtualWorkspaceSourceProjection(
        source_refs_by_virtual_path=refs,
        source_metadata_by_path={PATH: {}},
        source_projections_by_virtual_path=positions,
    )
    context = snapshot(
        RuntimeSourceBindingContextCache(), source_projection, CountingParser()
    )
    refs[PATH] = SourcePixelRef("disk", "/source/replaced.tif")
    positions.clear()
    assert context.source_paths_by_virtual_path[PATH] == "/source/original.tif"
    assert context.source_projections_by_virtual_path[PATH] is original_projection
    with pytest.raises(TypeError):
        context.source_projections_by_virtual_path[PATH] = original_projection


def test_resolved_direct_constructor_owns_deep_immutable_invariant():
    nested = {"Plate": "before"}
    resolved = ResolvedSourceMetadataRecord(((ORIGINAL_SOURCE_METADATA_FIELD, nested),))
    nested["Plate"] = "after"
    assert resolved[ORIGINAL_SOURCE_METADATA_FIELD]["Plate"] == "before"
    with pytest.raises(TypeError):
        resolved[ORIGINAL_SOURCE_METADATA_FIELD]["Plate"] = "invalid"
    with pytest.raises(TypeError, match="Source metadata scalar values"):
        ResolvedSourceMetadataRecord((("nested", {"unsupported": {"deep": 1}}),))


@pytest.mark.parametrize("context_owned", (False, True))
def test_warmed_cache_transport_reconstructs_all_derived_defaults(context_owned):
    processing_context = ProcessingContext(axis_id="A01")
    cache = (
        processing_context.runtime_source_binding_context_cache
        if context_owned
        else RuntimeSourceBindingContextCache()
    )
    parser = CountingParser()
    source_projection = projection({ORIGINAL_SOURCE_METADATA_FIELD: {"Plate": "A"}})
    context = snapshot(cache, source_projection, parser)
    cache.normalized_source_metadata(source_projection.source_metadata_by_path)
    assert cache.source_resolution_snapshots
    assert cache.source_metadata_by_mapping_identity
    restored_owner = pickle.loads(
        pickle.dumps(processing_context if context_owned else cache)
    )
    restored = (
        restored_owner.runtime_source_binding_context_cache
        if context_owned
        else restored_owner
    )
    if context_owned:
        assert restored_owner.axis_id == "A01"
    assert restored == RuntimeSourceBindingContextCache()
    rebuilt = snapshot(restored, source_projection, parser)
    assert rebuilt is not context
    assert rebuilt.metadata_for_path(PATH) == context.metadata_for_path(PATH)


def test_durable_workspace_mapping_still_runs_selector_parser_and_rule_fallbacks():
    from openhcs.core.source_metadata import DurableSourceMetadata, SourceMetadataRecord

    metadata = DurableSourceMetadata.from_mapping({"site": 8, "literal": "kept"})
    parser = CountingParser()
    context = SourcePatternResolutionContext.from_sources(
        parser=parser,
        source_paths_by_virtual_path={PATH: "/source/image.tif"},
        source_metadata_by_path={PATH: metadata},
        metadata_rules=(
            MetadataExtractionRule(
                source=MetadataSource.FILE_NAME, pattern=r"(?P<Plate>A01)"
            ),
        ),
    )
    assert not isinstance(metadata, SourceMetadataRecord)
    assert isinstance(
        context.source_metadata_by_path[PATH], DeclaredSourceMetadataRecord
    )
    resolved = context.metadata_for_path(PATH)
    assert resolved["site"] == 8
    assert resolved["well"] == "A01"
    assert resolved["literal"] == "kept"
    assert resolved[ORIGINAL_SOURCE_METADATA_FIELD]["Plate"] == "A01"
    assert parser.calls == [PATH]
