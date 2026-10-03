"""Metadata mapping order is not identity; values and plane order are."""
from collections.abc import Mapping

from openhcs.core.source_image_provenance import SourceImageIdentity, SourceImageProvenancePlanes
from openhcs.core.source_metadata import OriginalSourceMetadata, SourceFilterPathMetadata


def source_records(*, literal_site="001"):
    metadata = {"well": "A01", "site": "1", "channel": "1", "z_index": "0"}
    OriginalSourceMetadata.from_mapping({"well": "A01", "site": literal_site, "z_index": "000"}).merge_into(
        metadata, path="/input/A01_z000.tif",
    )
    SourceFilterPathMetadata.from_paths(("A01_z000.tif", "/input/A01_z000.tif")).merge_into(
        metadata, path="/input/A01_z000.tif",
    )
    return metadata


def test_source_identity_nested_mapping_reorder_is_equivalent():
    metadata = source_records()
    reordered = {
        key: dict(reversed(tuple(value.items()))) if isinstance(value, Mapping) else value
        for key, value in reversed(tuple(metadata.items()))
    }
    before = SourceImageIdentity("/input/A01_z000.tif", metadata)
    after = SourceImageIdentity("/input/A01_z000.tif", reordered)
    assert dict(before.component_metadata) == metadata
    assert dict(after.component_metadata) == reordered
    assert before.identity == after.identity
    planes = SourceImageProvenancePlanes.from_components
    assert planes(paths=(before.path,), component_metadata=(metadata,)) == planes(
        paths=(after.path,), component_metadata=(reordered,),
    )


def test_source_identity_changed_nested_value_is_distinct():
    original = source_records()
    changed = source_records(literal_site="002")
    assert SourceImageIdentity("/input/A01_z000.tif", original).identity != SourceImageIdentity(
        "/input/A01_z000.tif", changed,
    ).identity


def test_source_identity_distinct_plane_order_is_not_equivalent():
    first = SourceImageIdentity("/input/A01_z000.tif", source_records())
    second = SourceImageIdentity("/input/A01_z001.tif", {"well": "A01", "z_index": "1"})
    planes = SourceImageProvenancePlanes.from_components
    forward = planes(paths=(first.path, second.path), component_metadata=(first.component_metadata, second.component_metadata))
    reverse = planes(paths=(second.path, first.path), component_metadata=(second.component_metadata, first.component_metadata))
    assert forward.identity != reverse.identity
    assert forward != reverse
