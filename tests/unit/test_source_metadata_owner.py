"""Owned metadata lifetime and its production provenance consumers."""

import pickle
from collections.abc import Mapping, Sequence

import cloudpickle
from types import MappingProxyType

import numpy as np
import pytest
from polystore.virtual_workspace import SourcePixelRef

from openhcs.constants.constants import AllComponents
from openhcs.core.artifacts import ImageArtifactType
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_metadata,
)
from openhcs.core.source_binding_selection import DeclaredSourceMetadataRecord
from openhcs.core.source_bindings import (
    SOURCE_BINDING_ALIAS_METADATA_FIELD,
)
from openhcs.core.source_image_provenance import (
    SourceImageIdentity,
    SourceImageProvenance,
    SourceImageProvenancePlanes,
    SourceImageProvenance,
    RuntimeSourceImageProvenancePlane,
    SourcePlaneIndexedMetadata,
    source_component_metadata_consensus,
)
from openhcs.core.source_matching import (
    source_component_metadata_items,
    source_component_metadata_value,
    source_component_metadata_values,
    source_metadata_value,
    with_source_component_metadata,
)
from openhcs.core.source_metadata import (
    ORIGINAL_SOURCE_METADATA_FIELD,
    DurableSourceMetadata,
    ResolvedSourceMetadataRecord,
    SourceMetadataRecord,
    SourceMetadataFields,
    source_metadata_scalar,
)
from openhcs.core.source_projection import OpenHCSPlaneAddress, SourcePlaneProjection
from openhcs.core.steps.function_output_identity import FunctionOutputIdentity
from openhcs.core.source_workspace_projection import (
    VirtualWorkspaceImagePayloadProjection,
    VirtualWorkspaceSourceProjection,
)
from openhcs.core.virtual_workspace_metadata import (
    VirtualWorkspaceSourceMetadataEntries,
)
from python_introspect import to_jsonable


@pytest.mark.parametrize("owner", (ResolvedSourceMetadataRecord, DurableSourceMetadata))
def test_owned_snapshot_detaches_nested_fields_and_preserves_record_contract(owner):
    nested = {"Well": "literal"}
    record = owner.from_mapping({"well": "A01", ORIGINAL_SOURCE_METADATA_FIELD: nested})
    nested["Well"] = "changed"
    assert source_metadata_value(record, "Well") == "literal"
    with pytest.raises(TypeError):
        record[ORIGINAL_SOURCE_METADATA_FIELD]["Well"] = "changed"
    with pytest.raises(TypeError):
        hash(record)
    declared = DeclaredSourceMetadataRecord.from_mapping(
        {"well": "A01", ORIGINAL_SOURCE_METADATA_FIELD: {"Well": "literal"}}
    )
    reversed_record = owner.from_mapping(
        {ORIGINAL_SOURCE_METADATA_FIELD: {"Well": "literal"}, "well": "A01"}
    )
    if isinstance(record, SourceMetadataRecord):
        assert record == declared
        assert record != reversed_record
    else:
        assert record != declared and declared != record
        assert record == reversed_record
        assert record == dict(declared)


def test_owned_lookup_keeps_first_duplicate_field_and_full_ordered_record():
    record = ResolvedSourceMetadataRecord((("well", "A01"), ("well", "A02")))
    assert record["well"] == "A01"
    assert tuple(record.items()) == (("well", "A01"), ("well", "A01"))
    assert record.fields == (("well", "A01"), ("well", "A02"))
    assert dict(record) == {"well": "A01"}
    assert record != ResolvedSourceMetadataRecord((("well", "A01"),))


def test_runtime_birth_canonicalizes_but_durable_and_derived_values_keep_literal_spelling(
    tmp_path,
):
    spelling = str(tmp_path / "unused" / ".." / "image.tif")
    durable = DurableSourceMetadata.from_mapping({"path": spelling})
    runtime = ResolvedSourceMetadataRecord.from_mapping(durable)
    assert durable["path"] == spelling
    assert runtime["path"] == str(tmp_path / "image.tif")
    derived = SourceMetadataFields.with_fields(runtime, {"new_path": spelling})
    assert isinstance(derived, DurableSourceMetadata)
    assert derived["path"] == str(tmp_path / "image.tif")
    assert derived["new_path"] == spelling
    projection = SourcePlaneProjection(
        address=OpenHCSPlaneAddress.from_values(
            well="A01", site="1", channel="1", z_index="1", timepoint="1"
        ),
        ref=SourcePixelRef("disk", "plane.tif"),
        source_metadata=derived,
    )
    assert projection.source_metadata["new_path"] == str(tmp_path / "image.tif")


def test_owned_scalar_identity_reuses_literal_metadata_but_not_mutable_carriers():
    fields = {"well": "A01", "channel": "1", "extension": ".tif"}
    owner = DurableSourceMetadata.from_mapping(fields)
    original = ImagePayloadMetadata(
        source_provenance=SourceImageProvenance(
            source_path="/input/source.tif",
            source_component_metadata=owner,
            source_image_names=("DNA",),
        )
    )
    first = original.replace_fields()
    second = original.with_source_context_from(original)
    assert first.source_provenance is not original.source_provenance
    assert (
        first.source_provenance.source_identity
        is not original.source_provenance.source_identity
    )
    assert first.source_component_metadata is owner
    assert second.source_component_metadata is owner
    assert (
        first.source_provenance.equality_identity
        == original.source_provenance.equality_identity
    )
    assert to_jsonable(first) == to_jsonable(original)
    first.source_provenance.source_identity.path = "/changed.tif"
    assert original.source_path == "/input/source.tif"
    assert second.source_path == "/input/source.tif"


def test_workspace_alias_projection_and_artifact_naming_preserve_owned_metadata():
    source = VirtualWorkspaceSourceMetadataEntries.normalize_metadata_fields(
        {"well": "A01", "channel": "1", SOURCE_BINDING_ALIAS_METADATA_FIELD: "DNA"}
    )
    payload = ImagePayloadMetadata().payload_with(np.ones((2, 2), dtype=np.float32))
    projected = VirtualWorkspaceImagePayloadProjection(
        source_metadata=source, source_alias="DNA"
    ).apply(payload)
    metadata = image_payload_metadata(projected)
    assert isinstance(metadata.source_component_metadata, DurableSourceMetadata)
    assert SOURCE_BINDING_ALIAS_METADATA_FIELD not in metadata.source_component_metadata
    named = ImageArtifactType.normalize_runtime_payload("DerivedDNA", projected)
    named_metadata = image_payload_metadata(named)
    assert (
        named_metadata.source_component_metadata is metadata.source_component_metadata
    )
    assert named_metadata.source_image_names == ("DerivedDNA",)
    assert metadata.source_image_names == ("DNA",)
    assert (
        named_metadata.source_provenance.source_image_provenance_planes.represented_source_image_names
        == ("DNA",)
    )


def test_owned_updates_replace_aliases_and_keep_original_literals():
    owner = DurableSourceMetadata.from_mapping(
        {
            "channel": "1",
            "ChannelNumber": "2",
            ORIGINAL_SOURCE_METADATA_FIELD: {"ChannelNumber": "literal"},
        }
    )
    updated = with_source_component_metadata(owner, AllComponents.CHANNEL, "3")
    assert isinstance(updated, DurableSourceMetadata)
    assert "ChannelNumber" not in updated
    assert source_metadata_value(updated, "ChannelNumber") == "literal"
    assert source_component_metadata_values(updated, AllComponents.CHANNEL) == ("3",)
    assert owner["channel"] == "1"


@pytest.mark.parametrize("owner", (ResolvedSourceMetadataRecord, DurableSourceMetadata))
def test_custom_scalar_remains_live_for_queries_and_new_fingerprints(owner):
    class MutableInteger(int):
        def __str__(self):
            return self.tag

        def __repr__(self):
            return self.tag

    value = MutableInteger(1)
    value.tag = "before"
    record = owner.from_mapping({"channel": value})
    first = SourceImageIdentity(component_metadata=record)
    assert source_component_metadata_value(record, AllComponents.CHANNEL) == "before"
    value.tag = "after"
    assert source_component_metadata_value(record, AllComponents.CHANNEL) == "after"
    assert SourceImageIdentity(component_metadata=record).identity != first.identity
    assert first.identity[1] == (("channel", "before"),)


def test_lazy_role_errors_are_unchanged_by_owned_construction():
    record = DurableSourceMetadata.from_mapping(
        {
            "channel": "1",
            "wellrow": "A",
            "wellcolumn": "bad",
            ORIGINAL_SOURCE_METADATA_FIELD: 7,
        }
    )
    assert source_component_metadata_value(record, AllComponents.CHANNEL) == "1"
    with pytest.raises(ValueError):
        source_component_metadata_value(record, AllComponents.WELL)
    with pytest.raises(RuntimeError, match="must be a mapping"):
        source_metadata_value(record, "channel")
    with pytest.raises(RuntimeError, match="must be a mapping"):
        source_component_metadata_values(record, AllComponents.CHANNEL)


@pytest.mark.parametrize("invalid", ([1], {"deep": {"unsupported": 1}}, object()))
def test_durable_metadata_keeps_existing_invalid_value_domain(invalid):
    with pytest.raises(RuntimeError):
        VirtualWorkspaceSourceMetadataEntries.normalize_metadata_fields(
            {"field": invalid}
        )


def test_source_identity_mapping_equality_keeps_original_class_and_current_field_boundaries():
    owner = DurableSourceMetadata.from_mapping({"flag": True})
    identity = SourceImageIdentity("source.tif", owner)
    raw = SourceImageIdentity("source.tif", MappingProxyType({"flag": True}))
    assert identity == raw and raw == identity
    assert identity != SourceImageIdentity("source.tif", {"flag": 1})
    assert SourceImageIdentity(component_metadata=None) != SourceImageIdentity(
        component_metadata={}
    )
    with pytest.raises(TypeError):
        hash(identity)

    class Child(SourceImageIdentity):
        pass

    assert identity.__eq__(Child("source.tif", owner)) is NotImplemented

    class ReportedIdentity:
        @property
        def __class__(self):
            return SourceImageIdentity

        def __getattribute__(self, name):
            if name in ("path", "component_metadata", "_identity"):
                reads.append(name)
                return getattr(raw, name)
            return object.__getattribute__(self, name)

    reads = []
    assert identity.__eq__(ReportedIdentity()) is True
    assert reads == ["path", "component_metadata", "_identity"]

    nested = {"literal": "before"}
    left = SourceImageIdentity(
        component_metadata={ORIGINAL_SOURCE_METADATA_FIELD: nested}
    )
    right = SourceImageIdentity(
        component_metadata={ORIGINAL_SOURCE_METADATA_FIELD: {"literal": "before"}}
    )
    captured = left.identity
    assert left == right
    nested["literal"] = "after"
    assert left != right and left.identity == captured


def test_nested_mapping_order_does_not_change_provenance_identity_or_wire_order():
    raw = {"well": "A01", ORIGINAL_SOURCE_METADATA_FIELD: {"site": "001", "channel": "1"}}
    reordered = {ORIGINAL_SOURCE_METADATA_FIELD: {"channel": "1", "site": "001"}, "well": "A01"}
    owned = DurableSourceMetadata.from_mapping(reordered)
    before = to_jsonable(owned)
    original = SourceImageProvenance(source_path="source.tif", source_component_metadata=raw)
    for metadata in (reordered, owned):
        candidate = SourceImageProvenance(source_path="source.tif", source_component_metadata=metadata)
        assert candidate == original
        assert candidate.equality_identity == original.equality_identity
    assert SourceMetadataFields.provenance_identity_items(raw) == SourceMetadataFields.provenance_identity_items(owned)
    assert to_jsonable(owned) == before
    assert tuple(reordered) == (ORIGINAL_SOURCE_METADATA_FIELD, "well")
    assert tuple(reordered[ORIGINAL_SOURCE_METADATA_FIELD]) == ("channel", "site")
    reordered[ORIGINAL_SOURCE_METADATA_FIELD]["site"] = "002"
    changed = SourceImageProvenance(source_path="source.tif", source_component_metadata=reordered)
    assert changed.equality_identity != original.equality_identity


def test_canonical_metadata_identity_preserves_ordered_provenance_planes():
    paths = ("a.tif", "b.tif")
    metadata = ({"site": "1"}, {"site": "2"})
    forward = SourceImageProvenancePlanes.from_components(paths=paths, component_metadata=metadata)
    reverse = SourceImageProvenancePlanes.from_components(
        paths=tuple(reversed(paths)), component_metadata=tuple(reversed(metadata)),
    )
    assert SourceImageProvenance(source_image_provenance_planes=forward).equality_identity != SourceImageProvenance(
        source_image_provenance_planes=reverse,
    ).equality_identity


@pytest.mark.parametrize("serializer", (pickle, cloudpickle))
def test_identity_transport_preserves_birth_fingerprint_after_current_metadata_changes(serializer):
    from openhcs.core.orchestrator.execution_result import RuntimeExecutionTransportSerialization

    RuntimeExecutionTransportSerialization.register()
    nested = {"site": "001", "channel": "1"}
    identity = SourceImageIdentity("original.tif", {ORIGINAL_SOURCE_METADATA_FIELD: nested})
    birth = identity.identity
    nested["site"] = "002"
    identity.path = "current.tif"
    restored = serializer.loads(serializer.dumps(identity))
    assert restored.path == "current.tif"
    assert restored.component_metadata[ORIGINAL_SOURCE_METADATA_FIELD]["site"] == "002"
    assert restored.identity == birth
    assert SourceImageIdentity(restored.path, restored.component_metadata).identity != birth


def test_raw_composition_snapshots_once_before_consensus_reads():
    class ObservableMapping(Mapping):
        def __init__(self, values):
            self.values = values
            self.key_reads = self.value_reads = 0

        def __iter__(self):
            self.key_reads += 1
            return iter(self.values)

        def __len__(self):
            return len(self.values)

        def __getitem__(self, key):
            self.value_reads += 1
            return self.values[key]

    raw = ObservableMapping({"well": "A01"})
    consensus = source_component_metadata_consensus((raw, raw))
    assert dict(consensus) == {"well": "A01"}
    assert raw.key_reads == 2 and raw.value_reads == 2
    snapshot = SourceMetadataFields.composition_snapshot(raw)
    raw.values["well"] = "A02"
    assert snapshot["well"] == "A01"
    assert source_component_metadata_consensus((raw, raw))["well"] == "A02"


@pytest.mark.parametrize("owner", (ResolvedSourceMetadataRecord, DurableSourceMetadata))
@pytest.mark.parametrize("serializer", (pickle, cloudpickle))
def test_owned_transport_stores_only_authoritative_fields_and_rebuilds_local_views(
    owner, serializer
):
    record = owner.from_mapping(
        {"well": "A01", ORIGINAL_SOURCE_METADATA_FIELD: {"literal": "value"}}
    )
    before = SourceImageIdentity(component_metadata=record).identity
    assert source_metadata_value(record, "literal") == "value"
    assert source_component_metadata_value(record, AllComponents.WELL) == "A01"
    assert record._views
    restored = serializer.loads(serializer.dumps(record))
    assert isinstance(restored, owner)
    assert restored.fields == record.fields
    assert not restored._views
    assert restored.metadata_contents is not record.metadata_contents
    assert to_jsonable(restored) == to_jsonable(record)
    assert SourceImageIdentity(component_metadata=restored).identity == before
    with pytest.raises(TypeError):
        restored[ORIGINAL_SOURCE_METADATA_FIELD]["literal"] = "changed"


@pytest.mark.parametrize("owner", (ResolvedSourceMetadataRecord, DurableSourceMetadata))
def test_transport_does_not_recanonicalize_stored_absolute_values_or_validate_unused_roles(
    owner, tmp_path
):
    directory = tmp_path / "original"
    directory.mkdir()
    spelling = str(directory / "image.tif")
    record = owner.from_mapping({"path": spelling, ORIGINAL_SOURCE_METADATA_FIELD: 7})
    before = SourceImageIdentity(component_metadata=record).identity
    directory.rmdir()
    target = tmp_path / "replacement"
    target.mkdir()
    directory.symlink_to(target, target_is_directory=True)
    assert str((directory / "image.tif").resolve()) != spelling
    restored = pickle.loads(pickle.dumps(record))
    assert restored["path"] == spelling
    assert SourceImageIdentity(component_metadata=restored).identity == before
    with pytest.raises(RuntimeError, match="must be a mapping"):
        source_metadata_value(restored, "unused")


def test_ordered_component_batch_matches_sequential_raw_updates():
    fields = {
        "Well": "old",
        "Site": "old",
        "ChannelNumber": "old",
        "ZIndex": "old",
        "Timepoint": "old",
        ORIGINAL_SOURCE_METADATA_FIELD: {"Well": "literal"},
    }
    components = tuple(
        (component, str(index)) for index, component in enumerate(AllComponents, 1)
    )
    raw = dict(fields)
    for component, value in components:
        raw = with_source_component_metadata(raw, component, value)
    record = DurableSourceMetadata.from_mapping(fields)
    updated = SourceMetadataFields.with_fields(record, {}, components=components)
    assert isinstance(updated, DurableSourceMetadata)
    assert to_jsonable(updated) == to_jsonable(raw)
    assert tuple(updated) == tuple(raw)
    assert source_metadata_value(updated, "Well") == "literal"


@pytest.mark.parametrize("existing_extension", (False, True))
def test_output_identity_batch_keeps_source_field_order_and_separate_storage_extension(
    existing_extension,
):
    fields = {"literal": "kept", "Well": "old"}
    if existing_extension:
        fields["extension"] = ".old"
    identity = FunctionOutputIdentity(
        component_values={"well": "A01", "channel": "1"},
        extension=".tif",
        source="control",
    )
    expected = dict(fields)
    expected.update(identity.component_values)
    for component, value in source_component_metadata_items(identity.component_values):
        expected = with_source_component_metadata(expected, component, value)
    actual = identity.component_metadata(DurableSourceMetadata.from_mapping(fields))
    assert tuple(actual.items()) == tuple(expected.items())
    assert to_jsonable(actual) == expected
    assert identity.filename_component_metadata()["extension"] == ".tif"


def test_duplicate_record_keys_collapse_at_source_identity_mapping_boundary():
    record = ResolvedSourceMetadataRecord((("well", "A01"), ("well", "A02")))
    expected = SourceImageIdentity(component_metadata=dict(record))
    actual = SourceImageIdentity(component_metadata=record)
    assert actual == expected
    assert actual.identity == expected.identity
    assert tuple(actual.component_metadata.items()) == (("well", "A01"),)
    assert record.fields == (("well", "A01"), ("well", "A02"))


def test_stringified_key_collisions_keep_platform_map_last_value_at_owned_birth():
    fields = {1: "first", "1": "last"}
    durable = VirtualWorkspaceSourceMetadataEntries.normalize_metadata_fields(fields)
    assert tuple(durable.items()) == (("1", "last"),)
    projection = SourcePlaneProjection(
        address=OpenHCSPlaneAddress.from_values(
            well="A01", site="1", channel="1", z_index="1", timepoint="1"
        ),
        ref=SourcePixelRef("disk", "plane.tif"),
        source_metadata=fields,
    )
    assert tuple(projection.source_metadata.items()) == (("1", "last"),)
    declaration = DeclaredSourceMetadataRecord.from_mapping(fields)
    assert declaration.fields == (("1", "first"), ("1", "last"))
    assert declaration["1"] == "first"


@pytest.mark.parametrize(
    "decoder",
    (
        ResolvedSourceMetadataRecord.from_mapping,
        DurableSourceMetadata.from_mapping,
        VirtualWorkspaceSourceMetadataEntries.normalize_metadata_fields,
    ),
)
def test_owned_map_birth_validates_overwritten_stringified_key_values(decoder):
    with pytest.raises((TypeError, RuntimeError)):
        decoder({1: [], "1": "valid"})


def test_mapping_and_ordered_record_equality_namespaces_stay_separate():
    ordered = ResolvedSourceMetadataRecord.from_mapping({"well": "A01", "site": "1"})
    reordered = ResolvedSourceMetadataRecord.from_mapping({"site": "1", "well": "A01"})
    mapping = DurableSourceMetadata.from_mapping(ordered)
    reordered_mapping = DurableSourceMetadata.from_mapping(reordered)
    assert ordered != reordered
    assert mapping == reordered_mapping
    assert mapping == dict(ordered) and dict(ordered) == mapping
    for record in (
        ordered,
        reordered,
        DeclaredSourceMetadataRecord.from_mapping(dict(ordered)),
    ):
        assert mapping != record and record != mapping
    assert hash(ordered) == hash(
        DeclaredSourceMetadataRecord.from_mapping(dict(ordered))
    )
    with pytest.raises(TypeError):
        hash(mapping)


@pytest.mark.parametrize(
    "factory",
    (
        lambda metadata: VirtualWorkspaceSourceMetadataEntries({"plane.tif": metadata}),
        lambda metadata: VirtualWorkspaceImagePayloadProjection(
            source_metadata=metadata
        ),
        lambda metadata: VirtualWorkspaceSourceProjection({}, {"plane.tif": metadata}),
        lambda metadata: RuntimeSourceImageProvenancePlane(SourceImageIdentity(component_metadata=metadata)),
        lambda metadata: SourcePlaneIndexedMetadata(metadata, 0, 1),
        lambda metadata: SourcePlaneProjection(
            address=OpenHCSPlaneAddress.from_values(
                well="A01", site="1", channel="1", z_index="1", timepoint="1"
            ),
            ref=SourcePixelRef("disk", "plane.tif"),
            source_metadata=metadata,
        ),
    ),
)
def test_public_mapping_field_carriers_keep_content_equality(factory):
    owner = DurableSourceMetadata.from_mapping({"well": "A01", "site": "1"})
    reordered = DurableSourceMetadata.from_mapping({"site": "1", "well": "A01"})
    raw = MappingProxyType({"well": "A01", "site": "1"})
    assert factory(owner) == factory(reordered)
    assert factory(owner) == factory(raw)
    assert factory(raw) == factory(owner)
    with pytest.raises(TypeError):
        hash(factory(owner))


def test_durable_tuple_birth_uses_mapping_last_value_policy():
    metadata = DurableSourceMetadata((("well", "A01"), ("well", "A02")))
    assert metadata.fields == (("well", "A02"),)
    assert metadata == {"well": "A02"}
    assert (
        SourceImageIdentity(component_metadata=metadata).identity
        == SourceImageIdentity(component_metadata={"well": "A02"}).identity
    )


def test_scalar_admission_preserves_primitives_subclasses_and_scalar_container_precedence():
    class Integer(int):
        pass

    class Real(float):
        pass

    class TextMapping(str, Mapping):
        pass

    values = (
        None,
        False,
        True,
        0,
        -3,
        1.25,
        "literal",
        Integer(7),
        Real(2.5),
        TextMapping("literal"),
    )
    for value in values:
        assert DurableSourceMetadata.normalized_scalar(value) is value
        assert source_metadata_scalar(value) is value
    assert isinstance(values[-1], Mapping)
    assert isinstance(values[-1], Sequence)


def test_durable_scalar_admission_preserves_rejected_container_and_scalar_errors():
    class MappingSequence(Mapping, Sequence):
        def __getitem__(self, key):
            raise KeyError(key)

        def __iter__(self):
            return iter(())

        def __len__(self):
            return 0

    container_error = (
        "virtual_workspace source metadata supports scalar values and "
        "one-level scalar mappings only."
    )
    scalar_error = (
        "virtual_workspace source metadata scalar values must be strings, "
        "numbers, booleans, or null."
    )
    for value in (
        {},
        [],
        (),
        range(1),
        b"bytes",
        bytearray(b"bytes"),
        MappingSequence(),
    ):
        with pytest.raises(RuntimeError) as caught:
            DurableSourceMetadata.normalized_scalar(value)
        assert str(caught.value) == container_error
    for value in (set(), frozenset(), 1j, object()):
        with pytest.raises(RuntimeError) as caught:
            DurableSourceMetadata.normalized_scalar(value)
        assert str(caught.value) == scalar_error


def test_scalar_admission_keeps_none_identity_and_reported_class_read_order():
    class ReportedClass:
        def __init__(self, reports):
            self.reports = reports
            self.reads = []

        @property
        def __class__(self):
            reported = self.reports[min(len(self.reads), len(self.reports) - 1)]
            self.reads.append(reported)
            return reported

    reported_none = ReportedClass((type(None),))
    with pytest.raises(RuntimeError) as caught:
        DurableSourceMetadata.normalized_scalar(reported_none)
    assert str(caught.value) == (
        "virtual_workspace source metadata scalar values must be strings, "
        "numbers, booleans, or null."
    )
    assert reported_none.reads == [type(None)] * 6

    reported_none = ReportedClass((type(None),))
    with pytest.raises(TypeError, match="Source metadata scalar values must be"):
        source_metadata_scalar(reported_none)
    assert reported_none.reads == [type(None)] * 4

    reported_integer = ReportedClass((object, int, object))
    assert DurableSourceMetadata.normalized_scalar(reported_integer) is reported_integer
    assert reported_integer.reads == [object, int]

    for normalize in (
        source_metadata_scalar,
        SourceMetadataFields.normalized_scalar,
        ResolvedSourceMetadataRecord.normalized_scalar,
    ):
        reported_integer = ReportedClass((object, int, object))
        assert normalize(reported_integer) is reported_integer
        assert reported_integer.reads == [object, int, object]

        # Scalar admission and string normalization are separate observations.
        # A changing reported class must retain the previous normalization order.
        reported_string = ReportedClass((str, object))
        assert normalize(reported_string) is reported_string
        assert reported_string.reads == [str, object]

    reported_string = ReportedClass((str, object))
    assert DurableSourceMetadata.normalized_scalar(reported_string) is reported_string
    assert reported_string.reads == [str]

    changing_class = ReportedClass(
        (object, object, object, object, object, Sequence, str)
    )
    with pytest.raises(RuntimeError) as caught:
        DurableSourceMetadata.normalized_scalar(changing_class)
    assert str(caught.value) == (
        "virtual_workspace source metadata scalar values must be strings, "
        "numbers, booleans, or null."
    )
    assert changing_class.reads == [
        object,
        object,
        object,
        object,
        object,
        Sequence,
        str,
    ]
