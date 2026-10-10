from types import MappingProxyType

import pytest

from openhcs.core.source_binding_selection import DeclaredSourceMetadataRecord
from openhcs.core.source_matching import (
    ORIGINAL_SOURCE_METADATA_FIELD,
    semantic_source_metadata_value,
    source_component_metadata_value,
    source_component_metadata_values,
    source_metadata_value,
)
from openhcs.domains.microscopy.axes import Microscopy


@pytest.mark.parametrize("readonly_outer", (False, True))
def test_metadata_queries_observe_scalar_mutation(readonly_outer):
    backing = {"well": "A01"}
    metadata = MappingProxyType(backing) if readonly_outer else backing

    assert source_metadata_value(metadata, "well") == "A01"
    assert semantic_source_metadata_value(metadata, "well") == "A01"
    assert source_component_metadata_values(metadata, Microscopy.Well) == ("A01",)

    backing["well"] = "A02"

    assert source_metadata_value(metadata, "well") == "A02"
    assert semantic_source_metadata_value(metadata, "well") == "A02"
    assert source_component_metadata_value(metadata, Microscopy.Well) == "A02"
    assert source_component_metadata_values(metadata, Microscopy.Well) == ("A02",)


@pytest.mark.parametrize(
    "view", (dict, MappingProxyType, DeclaredSourceMetadataRecord.from_mapping)
)
def test_literal_queries_observe_nested_original_mutation(view):
    original = {"Well": "LiteralA"}
    metadata = view({"well": "A01", ORIGINAL_SOURCE_METADATA_FIELD: original})

    assert source_metadata_value(metadata, "Well") == "LiteralA"
    assert semantic_source_metadata_value(metadata, "Well") == "LiteralA"

    original["Well"] = "LiteralB"

    assert source_metadata_value(metadata, "Well") == "LiteralB"
    assert semantic_source_metadata_value(metadata, "Well") == "LiteralB"
    assert source_component_metadata_value(metadata, Microscopy.Well) == "A01"
    assert source_component_metadata_values(metadata, Microscopy.Well) == ("A01",)


def test_live_alias_queries_preserve_priority_cardinality_and_null_fallback():
    original = {"ChannelNumber": "literal"}
    metadata = {
        "ChannelNumber": "2",
        "channel": "1",
        "Metadata_Channel": "2",
        ORIGINAL_SOURCE_METADATA_FIELD: original,
    }
    assert source_metadata_value(metadata, "ChannelNumber") == "literal"
    assert source_component_metadata_value(metadata, Microscopy.Channel) == "1"
    assert source_component_metadata_values(metadata, Microscopy.Channel) == (
        "1",
        "2",
    )

    original["ChannelNumber"] = None
    metadata["channel"] = None
    metadata["ChannelNumber"] = "3"
    metadata["Metadata_Channel"] = "3"

    assert source_metadata_value(metadata, "ChannelNumber") == "3"
    assert semantic_source_metadata_value(metadata, "ChannelNumber") == "3"
    assert source_component_metadata_value(metadata, Microscopy.Channel) == "3"
    assert source_component_metadata_values(metadata, Microscopy.Channel) == ("3",)

    del metadata["ChannelNumber"]
    metadata["Metadata_Channel"] = None

    assert source_metadata_value(metadata, "ChannelNumber") is None
    assert semantic_source_metadata_value(metadata, "ChannelNumber") is None
    assert source_component_metadata_values(metadata, Microscopy.Channel) == ()
