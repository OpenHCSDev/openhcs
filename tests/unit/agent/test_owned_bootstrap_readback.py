"""Provider-free witnesses for the diagnostic's complete publication checks."""

import pytest

from polystore.virtual_workspace import SourcePixelRef
from openhcs.agent.dto.execution import ArtifactMaterializationPlanSummary, ArtifactPlanSummary
from openhcs.core.artifacts import ImageArtifactType
from openhcs.core.source_projection import OpenHCSPlaneAddress, SourceArtifactProjection, SourcePlaneProjection
from openhcs.processing.custom_functions.manager import CustomFunctionManager
from tests.diagnostics.check_owned_bootstrap_live import fixture_registration_sources
from tests.diagnostics.owned_bootstrap_readback import require_csv_rows, require_projection_inventory


def image_plan(name="probe_image"):
    return ArtifactPlanSummary(name=name, kind="image", path=f"/runtime/{name}",
        materialization=ArtifactMaterializationPlanSummary(persistent_enabled=True))


def projections_for(addresses, name="probe_image"):
    return tuple(SourcePlaneProjection(address, SourcePixelRef("disk", f"main-{index}.tif"))
                 for index, address in enumerate(addresses)) + tuple(
        SourceArtifactProjection(address, SourcePixelRef("disk", f"{name}-{index}.tif"),
                                 name, ImageArtifactType)
        for index, address in enumerate(addresses))


def test_named_and_primary_inventory_is_complete_and_extends_from_declarations():
    addresses = tuple(OpenHCSPlaneAddress.from_values("image.ome.tif", 1, 1, z, 1) for z in (3, 1))
    saved = projections_for(addresses)
    require_projection_inventory(saved, addresses, (image_plan(),))
    with pytest.raises(AssertionError):
        require_projection_inventory(saved[:2], addresses, (image_plan(),))
    with pytest.raises(AssertionError):
        require_projection_inventory(saved[2:], addresses, (image_plan(),))
    with pytest.raises(AssertionError):
        require_projection_inventory(saved, addresses, (image_plan(), image_plan("new_case")))
    more = projections_for(addresses, "new_case")[2:]
    require_projection_inventory(saved + more, addresses, (image_plan(), image_plan("new_case")))


@pytest.mark.parametrize("field", ["well", "site", "channel", "z_index", "timepoint"])
def test_csv_address_cannot_match_only_slice_label_and_count(field):
    address = OpenHCSPlaneAddress.from_values("image.ome.tif", 1, 2, 3, 4)
    row = dict(address.as_component_metadata(), slice_index="0", object_label="13",
               pixel_count="16", object_name="probe_labels")
    expected = ((0, 13, 16),)
    require_csv_rows((row,), expected, (address,), "probe_labels")
    row[field] = "foreign" if field == "well" else "99"
    with pytest.raises(AssertionError):
        require_csv_rows((row,), expected, (address,), "probe_labels")


def test_each_fixture_registration_source_has_one_original_declaration():
    manager = CustomFunctionManager(create_storage=False)
    sources = fixture_registration_sources()
    assert tuple(name for name, _code in sources) == (
        "select_volume_fixture_planes_v2", "inspect_volume_fixture_v2")
    for name, code in sources:
        metadata = manager._prepare_source(code)
        assert metadata.original_name == name
