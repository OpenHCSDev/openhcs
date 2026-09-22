"""Identity-sanitization tests; no biological pipeline execution."""
import xml.etree.ElementTree as ET

import pytest

from benchmark.prepare_blind_neurite import (
    Channel, IDENTITY_PROPERTIES, assert_no_identity_leak,
    cleanup_aborted_identity_order, sanitize_metadata,
)


def metadata_xml() -> str:
    root = ET.Element("MetaData")
    values = {
        "Description": "Plate Name: F04-controls\nFolder Name: Tristan\nB-C: Y27 EpoB\nExposure: 10 ms\nBinning: 2 x 2",
        "_IllumSetting_": "FITC",
        "spatial-calibration-state": "on",
        "spatial-calibration-x": "1.3556",
        "spatial-calibration-y": "1.3556",
        "spatial-calibration-units": "um",
        "stage-label": "B02 : Site 1",
        "SiteX": "1", "SiteY": "1", "OffsetFromWellCenterUmX": "-1249.5",
        **{identity: "original_identifier" for identity in IDENTITY_PROPERTIES},
    }
    for identity, value in values.items():
        ET.SubElement(root, "prop", id=identity, value=value)
    return ET.tostring(root, encoding="unicode")


def test_metadata_identity_is_removed_without_acquisition_changes() -> None:
    original = metadata_xml()
    result = sanitize_metadata(original, "A47", 1, Channel.FITC)
    props = {e.attrib["id"]: e.attrib["value"] for e in ET.fromstring(result.xml)}
    assert result.original_xml == original
    assert result.calibration_um == (1.3556, 1.3556)
    assert set(result.removed_property_ids) == IDENTITY_PROPERTIES
    assert props["stage-label"] == "A47 : Site 1"
    assert props["Description"] == "Exposure: 10 ms\nBinning: 2 x 2"
    assert props["OffsetFromWellCenterUmX"] == "-1249.5"
    assert props["SiteX"] == "1"
    assert_no_identity_leak(result.xml)


def test_unknown_description_fails_closed() -> None:
    with pytest.raises(ValueError, match="Unknown description layout"):
        sanitize_metadata(metadata_xml().replace("Exposure:", "Unrecognized:"), "A01", 1, Channel.FITC)


def test_unexpected_calibration_fails_closed() -> None:
    with pytest.raises(ValueError, match="Unexpected calibration"):
        sanitize_metadata(metadata_xml().replace("1.3556", "1.0"), "A01", 1, Channel.FITC)


def test_illumination_disagreement_fails_closed() -> None:
    with pytest.raises(ValueError, match="Filename channel differs"):
        sanitize_metadata(metadata_xml(), "A01", 1, Channel.DAPI)


def test_leaked_identifier_fails_closed() -> None:
    with pytest.raises(ValueError, match="Identity-bearing metadata survived"):
        sanitize_metadata(metadata_xml().replace("10 ms", "DMSO"), "A01", 1, Channel.FITC)


def test_cleanup_refuses_wrong_task_root(tmp_path) -> None:
    with pytest.raises(ValueError, match="Unexpected private task-root identity"):
        cleanup_aborted_identity_order(tmp_path / "inputs", tmp_path / "not-a-key-root")


def test_cleanup_refuses_missing_final_receipt(tmp_path) -> None:
    with pytest.raises(ValueError, match="Final private receipt missing"):
        cleanup_aborted_identity_order(tmp_path / "inputs", tmp_path / "neurite-source-key")
