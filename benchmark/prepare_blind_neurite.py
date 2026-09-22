"""Lossless, identity-sanitized input staging; never performs biological analysis.

The private receipt contains original identities/XML. Do not expose that receipt,
this preparation context, or the source tree to the blinded pipeline author.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, replace
from enum import Enum
import hashlib
import json
import os
from pathlib import Path
import random
import re
import secrets
import shutil
import xml.etree.ElementTree as ET

import numpy as np
import tifffile

from openhcs.serialization.json import to_jsonable


class Channel(Enum):
    DAPI = (1, "DAPI")
    FITC = (2, "FITC")

    @property
    def number(self) -> int:
        return self.value[0]

    @property
    def illumination(self) -> str:
        return self.value[1]

    @classmethod
    def from_number(cls, number: int) -> Channel:
        return next(channel for channel in cls if channel.number == number)


@dataclass(frozen=True)
class SourceImage:
    path: Path
    well: str
    site: int
    channel: Channel


@dataclass(frozen=True)
class SanitizedMetadata:
    xml: str
    original_xml: str
    removed_property_ids: tuple[str, ...]
    calibration_um: tuple[float, float]


@dataclass(frozen=True)
class PrivateImageReceipt:
    source_path: str
    source_well: str
    site: int
    channel: Channel
    coded_relative_path: str
    source_file_sha256: str
    staged_file_sha256: str
    pixel_sha256: str
    shape: tuple[int, int]
    dtype: str
    original_xml: str
    removed_property_ids: tuple[str, ...]
    calibration_um: tuple[float, float]


@dataclass(frozen=True)
class PrivatePreparationReceipt:
    protocol_version: int
    opaque_random_seed: str
    author_root: str
    identity_redactions: tuple[str, ...]
    images: tuple[PrivateImageReceipt, ...]


@dataclass(frozen=True)
class DiscardedTaskFile:
    relative_path: str
    bytes: int
    sha256: str


@dataclass(frozen=True)
class AbortedPreparationCleanup:
    removed_exact_root: str
    file_count: int
    bytes_reclaimed: int
    reason: str
    files: tuple[DiscardedTaskFile, ...]


IDENTITY_PROPERTIES = frozenset(
    {
        "plane-guid",
        "acquisition-time-local",
        "modification-time-local",
        "stage-position-x",
        "stage-position-y",
        "z-position",
        "ImageXpress Micro X",
        "ImageXpress Micro Y",
        "ImageXpress Micro Z",
        "Instrument Serial Number",
    }
)
IDENTITY_TOKENS = (
    "F04",
    "analogs",
    "controls",
    "24098",
    "24099",
    "Tristan",
    "09-027",
    "06-049",
    "09-037",
    "08-115",
    "09-079",
    "FC-A",
    "EpoB",
    "DMSO",
    "Y27",
)
SOURCE_FILENAME = re.compile(r".+_([B-G](?:0[2-9]|1[01]))_s([1-9])_w([12])\.TIF")
SOURCE_TAG_CODES = frozenset(
    {254, 256, 257, 258, 259, 262, 270, 273, 274, 277, 278, 279, 305, 306}
)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def pixel_sha256(image: np.ndarray) -> str:
    return hashlib.sha256(np.ascontiguousarray(image).tobytes()).hexdigest()


def assert_no_identity_leak(text: str) -> None:
    folded = text.casefold()
    found = tuple(token for token in IDENTITY_TOKENS if token.casefold() in folded)
    if found:
        raise ValueError(f"Identity-bearing metadata survived: {found}")


def sanitize_metadata(
    original_xml: str, coded_well: str, site: int, channel: Channel
) -> SanitizedMetadata:
    root = ET.fromstring(original_xml)
    props = {
        element.attrib["id"]: element
        for element in root.iter()
        if "id" in element.attrib
    }
    if props["_IllumSetting_"].attrib["value"] != channel.illumination:
        raise ValueError("Filename channel differs from acquisition illumination")
    if props["spatial-calibration-state"].attrib["value"] != "on":
        raise ValueError("Spatial calibration disabled")
    calibration = tuple(
        float(props[key].attrib["value"])
        for key in ("spatial-calibration-x", "spatial-calibration-y")
    )
    if (
        calibration != (1.3556, 1.3556)
        or props["spatial-calibration-units"].attrib["value"] != "um"
    ):
        raise ValueError("Unexpected calibration; refuse silent geometry changes")
    description = props["Description"].attrib["value"]
    prefix, separator, acquisition = description.partition("Exposure:")
    if not separator or "Plate Name:" not in prefix:
        raise ValueError("Unknown description layout; refuse broad metadata deletion")
    props["Description"].set("value", "Exposure:" + acquisition)
    props["stage-label"].set("value", f"{coded_well} : Site {site}")
    removed: list[str] = []
    for parent in root.iter():
        for element in tuple(parent):
            if "id" in element.attrib and element.attrib["id"] in IDENTITY_PROPERTIES:
                removed.append(element.attrib["id"])
                parent.remove(element)
    if set(removed) != IDENTITY_PROPERTIES:
        raise ValueError("Unexpected acquisition identity schema")
    xml = ET.tostring(root, encoding="unicode")
    assert_no_identity_leak(xml)
    return SanitizedMetadata(xml, original_xml, tuple(sorted(removed)), calibration)


def inventory_plate(root: Path) -> tuple[SourceImage, ...]:
    images: list[SourceImage] = []
    for path in sorted(root.rglob("*.TIF")):
        match = SOURCE_FILENAME.fullmatch(path.name)
        if match is None:
            raise ValueError(f"Unexpected raw filename: {path}")
        well, site, channel = match.groups()
        images.append(
            SourceImage(path, well, int(site), Channel.from_number(int(channel)))
        )
    expected = {
        (f"{row}{column:02}", site, channel)
        for row in "BCDEFG"
        for column in range(2, 12)
        for site in range(1, 10)
        for channel in Channel
    }
    actual = {(image.well, image.site, image.channel) for image in images}
    if len(images) != 1080 or actual != expected:
        raise ValueError(
            "Incomplete/duplicate acquisition; no missing field is filled with zero"
        )
    return tuple(images)


def stage_image(
    source: SourceImage, destination: Path, coded_well: str
) -> PrivateImageReceipt:
    original_hash = sha256_file(source.path)
    with tifffile.TiffFile(source.path) as tiff:
        if (
            len(tiff.pages) != 1
            or {tag.code for tag in tiff.pages[0].tags.values()} != SOURCE_TAG_CODES
        ):
            raise ValueError("Unexpected TIFF page/tag schema")
        page = tiff.pages[0]
        pixels = page.asarray()
        if pixels.shape != (1024, 1024) or pixels.dtype != np.dtype("uint16"):
            raise ValueError("Unexpected raw image geometry")
        source_props = {
            e.attrib["id"]: e.attrib["value"]
            for e in ET.fromstring(page.description).iter()
            if "id" in e.attrib
        }
        if source_props["stage-label"] != f"{source.well} : Site {source.site}":
            raise ValueError("Filename and acquisition field identity differ")
        metadata = sanitize_metadata(
            page.description, coded_well, source.site, source.channel
        )
        if (
            page.photometric != tifffile.PHOTOMETRIC.MINISBLACK
            or int(page.tags[274].value) != 1
        ):
            raise ValueError("Unexpected pixel display/orientation semantics")
        destination.parent.mkdir(parents=True, exist_ok=True)
        tifffile.imwrite(
            destination,
            pixels,
            photometric="minisblack",
            metadata=None,
            description=metadata.xml,
            software=page.tags[305].value,
            byteorder=tiff.byteorder,
            rowsperstrip=page.rowsperstrip,
            subfiletype=int(page.tags[254].value),
            extratags=[(274, "H", 1, 1, False)],
        )
    with tifffile.TiffFile(destination) as staged:
        copied = staged.asarray()
        if not np.array_equal(copied, pixels) or copied.dtype != pixels.dtype:
            raise ValueError("Staged pixels differ from original")
        assert_no_identity_leak(staged.pages[0].description)
        if 306 in staged.pages[0].tags:
            raise ValueError("Original acquisition timestamp survived")
        copied_props = {
            e.attrib["id"]: e.attrib["value"]
            for e in ET.fromstring(staged.pages[0].description).iter()
            if "id" in e.attrib
        }
        if (
            tuple(
                float(copied_props[k])
                for k in ("spatial-calibration-x", "spatial-calibration-y")
            )
            != metadata.calibration_um
        ):
            raise ValueError("Staged calibration differs")
    if sha256_file(source.path) != original_hash:
        raise ValueError("Original source changed while staging")
    # Neutral filesystem timestamps also avoid disclosing acquisition/write order.
    os.utime(destination, (1789430400, 1789430400))
    return PrivateImageReceipt(
        str(source.path),
        source.well,
        source.site,
        source.channel,
        str(destination.name),
        original_hash,
        sha256_file(destination),
        pixel_sha256(pixels),
        pixels.shape,
        str(pixels.dtype),
        metadata.original_xml,
        metadata.removed_property_ids,
        metadata.calibration_um,
    )


def prepare(
    source_root: Path, author_root: Path, private_root: Path
) -> PrivatePreparationReceipt:
    if author_root.exists() or private_root.exists():
        raise FileExistsError(
            "Task roots must be new; never overwrite a staged corpus/key"
        )
    if source_root.resolve() in (author_root.resolve(), private_root.resolve()):
        raise ValueError("Source and task roots must differ")
    if (
        author_root.resolve() in private_root.resolve().parents
        or private_root.resolve() in author_root.resolve().parents
    ):
        raise ValueError("Private evaluation and author roots must be disjoint")
    plates = tuple(sorted(path for path in source_root.iterdir() if path.is_dir()))
    if len(plates) != 2:
        raise ValueError("Expected exactly two acquisition plates")
    inventories = {plate: inventory_plate(plate) for plate in plates}
    if shutil.disk_usage(author_root.parent).free < 5_000_000_000:
        raise ValueError("Insufficient external-drive space")
    seed = secrets.token_hex(32)
    generator = random.Random(int(seed, 16))
    shuffled_plates = list(plates)
    generator.shuffle(shuffled_plates)
    staging_root = author_root.parent / (".blind-staging-" + secrets.token_hex(8))
    staging_root.mkdir()
    private_root.mkdir(parents=True, mode=0o700)
    receipts: list[PrivateImageReceipt] = []
    for plate_number, plate in enumerate(shuffled_plates, 1):
        plate_id = f"P{plate_number:03}"
        wells = sorted({image.well for image in inventories[plate]})
        generator.shuffle(wells)
        well_codes = {well: f"A{number:02}" for number, well in enumerate(wells, 1)}
        # Create files in coded order, not the original physical-well order.
        for source in sorted(
            inventories[plate],
            key=lambda image: (
                well_codes[image.well],
                image.site,
                image.channel.number,
            ),
        ):
            coded_well = well_codes[source.well]
            filename = (
                f"{coded_well}_s{source.site:03}_w{source.channel.number}_z001_t001.tif"
            )
            destination = staging_root / plate_id / filename
            receipt = stage_image(source, destination, coded_well)
            receipts.append(
                replace(receipt, coded_relative_path=f"{plate_id}/{filename}")
            )
        print(
            f"Staged {plate_id}: 1080 images, 60 coded wells, 9 sites, 2 channels",
            flush=True,
        )
    receipt = PrivatePreparationReceipt(
        1,
        seed,
        str(author_root),
        (
            "Description identity/treatment prefix",
            "stage-label replaced with coded identity",
            "TIFF DateTime omitted",
            *tuple(sorted(IDENTITY_PROPERTIES)),
        ),
        tuple(receipts),
    )
    private_manifest = private_root / "private_source_key.json"
    private_manifest.write_text(json.dumps(to_jsonable(receipt), indent=2) + "\n")
    private_manifest.chmod(0o600)
    public_text = (
        "Neutral acquisition corpus. Two plates P001/P002, each 60 coded wells A01:A60, "
        "nine sites per well, two channels: w1 DAPI, w2 FITC. All images are scalar "
        "1024 x 1024 uint16; one timepoint and one Z plane. Spatial calibration "
        "is 1.3556 um/pixel in X/Y. Coded well IDs do not imply physical plate positions. "
        "Site numbers and relative within-well geometry are retained. No treatment "
        "labels, original well/plate identifiers, original acquisition times, "
        "absolute stage positions, or comparator values are supplied.\n"
    )
    (staging_root / "INPUT_CONTRACT.txt").write_text(public_text)
    if len(tuple(staging_root.rglob("*.tif"))) != 2160:
        raise ValueError("Unexpected staged image count")
    staging_root.rename(author_root)
    print(f"Author input root: {author_root}", flush=True)
    print(f"Private key root (do not expose to author): {private_root}", flush=True)
    print(f"Private receipt SHA256: {sha256_file(private_manifest)}", flush=True)
    return receipt


def cleanup_aborted_identity_order(
    author_root: Path, private_root: Path
) -> AbortedPreparationCleanup:
    """Authorized cleanup of one exact, validated interrupted task-copy directory."""
    aborted = private_root.with_name("neurite-source-key-aborted-identity-order")
    if private_root.name != "neurite-source-key" or aborted.is_symlink():
        raise ValueError("Unexpected private task-root identity")
    if not (private_root / "private_source_key.json").is_file():
        raise ValueError("Final private receipt missing")
    if len(tuple(author_root.rglob("*.tif"))) != 2160:
        raise ValueError("Final author corpus incomplete")
    if not aborted.is_dir() or tuple(aborted.iterdir()) != (
        aborted / "staging-residue",
    ):
        raise ValueError("Unexpected aborted contents; refuse deletion")
    files: list[DiscardedTaskFile] = []
    for item in sorted(aborted.rglob("*")):
        if item.is_symlink():
            raise ValueError("Symlink in aborted copy root; refuse deletion")
        if item.is_dir():
            if item.name not in {"staging-residue", "P001", "P002"}:
                raise ValueError("Unexpected aborted directory")
            continue
        if item.suffix != ".tif" or item.parent.name not in {"P001", "P002"}:
            raise ValueError("Unexpected aborted non-TIFF file")
        files.append(
            DiscardedTaskFile(
                str(item.relative_to(aborted)), item.stat().st_size, sha256_file(item)
            )
        )
    receipt = AbortedPreparationCleanup(
        str(aborted.resolve()),
        len(files),
        sum(file.bytes for file in files),
        "Interrupted preparation was superseded by coded-order creation and neutral timestamps",
        tuple(files),
    )
    receipt_path = private_root / "aborted_preparation_cleanup.json"
    receipt_path.write_text(json.dumps(to_jsonable(receipt), indent=2) + "\n")
    receipt_path.chmod(0o600)
    shutil.rmtree(aborted)
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--author-root", type=Path, required=True)
    parser.add_argument("--private-root", type=Path, required=True)
    arguments = parser.parse_args()
    prepare(arguments.source_root, arguments.author_root, arguments.private_root)


if __name__ == "__main__":
    main()
