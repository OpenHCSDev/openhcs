"""All source-metadata carriers decode authored aliases at the same boundary."""

from functools import partial

import numpy as np
import pytest

from openhcs.core.artifacts import ArtifactSpec, ObjectLabelsArtifactType
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_measurements import (
    MeasurementScope,
    MeasurementSubject,
    MeasurementTable,
)
from openhcs.core.runtime_object_labels import (
    ObjectLabelPayload,
    ObjectLabelSet,
    ObjectLabelVariantData,
)
from openhcs.core.runtime_relationships import (
    DirectedObjectRelationshipPayload,
    ObjectRelationship,
    ObjectRelationshipDeclaration,
)
from openhcs.core.runtime_spatial_graph import SpatialGraph
from openhcs.core.runtime_tabular_values import ColumnarRows
from openhcs.core.source_image_provenance import SourceImageProvenance


class EmptyRows(ColumnarRows):
    columns = {}
    fields = ()


def _carriers():
    labels = ObjectLabelVariantData(labels=np.zeros((2, 3), dtype=np.int32))
    relationship = ObjectRelationshipDeclaration.parent_child(
        source=ArtifactSpec.output("Cells", ObjectLabelsArtifactType).ref(),
        target=ArtifactSpec.output("Nuclei", ObjectLabelsArtifactType).ref(),
        producer_module_number=1,
    )
    return (
        ImagePayloadMetadata,
        partial(ObjectLabelPayload, variant_data=labels),
        partial(ObjectLabelSet, name="Cells", variant_data=labels),
        partial(
            MeasurementTable,
            name="Intensity",
            rows=EmptyRows(),
            subject=MeasurementSubject(MeasurementScope.SAMPLE, "DNA"),
        ),
        partial(SpatialGraph, name="Graph", nodes=(), edges=()),
        partial(
            ObjectRelationship,
            name="ParentChild",
            declaration=relationship,
            payload=DirectedObjectRelationshipPayload(source_ids=(), target_ids=()),
        ),
    )


@pytest.mark.parametrize("construct", _carriers())
def test_absent_aliases_do_not_create_empty_provenance(construct, monkeypatch):
    supplied = SourceImageProvenance(
        source_path="/tmp/source.tif", source_component_metadata={"well": "A01"}
    )

    def unexpected(cls, values):
        pytest.fail("Absent source aliases must not allocate a decoded value.")

    monkeypatch.setattr(
        SourceImageProvenance, "from_init_values", classmethod(unexpected)
    )
    carrier = construct(source_provenance=supplied)
    assert carrier.source_path == "/tmp/source.tif"
    assert carrier.source_component_metadata["well"] == "A01"
    assert carrier.source_provenance is not supplied
    carrier.source_provenance.source_identity.path = "/tmp/changed.tif"
    assert supplied.source_path == "/tmp/source.tif"


@pytest.mark.parametrize("construct", _carriers())
def test_explicit_empty_metadata_and_aliases_still_decode(construct, monkeypatch):
    calls = []
    original = SourceImageProvenance.from_init_values

    def observe(cls, values):
        calls.append(values)
        return original(values)

    monkeypatch.setattr(SourceImageProvenance, "from_init_values", classmethod(observe))
    empty = construct(source_component_metadata={})
    assert calls == [(None, {}, None, ())]
    assert empty.source_component_metadata is not None
    assert dict(empty.source_component_metadata) == {}
    authored = construct(source_path="/tmp/authored.tif", source_image_names=("DNA",))
    assert authored.source_path == "/tmp/authored.tif"
    assert authored.source_image_names == ("DNA",)
    assert len(calls) == 2
