"""ImageXpress TIFF acquisition semantics, without filename-axis replacement."""

from __future__ import annotations

from pathlib import Path
from xml.etree import ElementTree

from polystore.source_tile_geometry import SourceTileGeometry
from polystore.tiff_header import TiffImageHeader

from openhcs.core.source_metadata import (
    OriginalSourceMetadata,
    SourceMetadataMapping,
    SourceVoxelSpacing,
)
from openhcs.core.source_projection import SourcePlaneDataset
from openhcs.microscopes.bioformats_adapter import SourcePlaneStoreAdapter


class ImageXpressTiffSourceMetadataAdapter(SourcePlaneStoreAdapter):
    """Interpret exact MetaMorph PlaneInfo properties on ordinary raw TIFFs.

    OffsetFromWellCenterUmX/Y are acquisition-relative stage positions. ImageXpress
    SiteX/Y increase along array X/Y; coordinates are converted independently by
    the declared micrometer-per-pixel X/Y calibration. These offsets establish
    exact acquisition placement, not correlation-derived registration.
    """

    registry_key = "imagexpress_tiff_source_metadata"

    def discover_stores(self, root: Path) -> tuple[SourcePlaneDataset, ...]:
        # These ordinary files retain the declared filename binding identities.
        del root
        return ()

    def source_metadata_for_path(self, path: Path) -> SourceMetadataMapping:
        header = TiffImageHeader.read(path)
        if header is None or not header.description:
            return {}
        description = header.description.lstrip()
        if not description.startswith("<MetaData"):
            return {}
        root = ElementTree.fromstring(description)
        plane = root.find("PlaneInfo")
        if plane is None:
            return {}
        properties: dict[str, str] = {}
        for prop in plane:
            if prop.tag not in ("prop", "custom-prop"):
                continue
            key, value = prop.attrib["id"], prop.attrib["value"]
            if key in properties and properties[key] != value:
                raise ValueError(
                    f"Conflicting embedded TIFF property {key!r} in {path}."
                )
            properties[key] = value
        geometry_fields = (
            "OffsetFromWellCenterUmX",
            "OffsetFromWellCenterUmY",
            "SiteX",
            "SiteY",
        )
        if not any(key in properties for key in geometry_fields):
            return {}
        required = (
            *geometry_fields,
            "spatial-calibration-x",
            "spatial-calibration-y",
            "spatial-calibration-units",
            "spatial-calibration-state",
        )
        missing = tuple(key for key in required if key not in properties)
        if missing:
            raise ValueError(
                f"Incomplete ImageXpress tile geometry in {path}: {missing!r}."
            )
        if properties["spatial-calibration-state"] != "on":
            raise ValueError(
                f"ImageXpress tile geometry requires enabled calibration in {path}."
            )
        if properties["spatial-calibration-units"] not in ("um", "µm", "μm"):
            raise ValueError(
                f"ImageXpress tile geometry requires micrometer units in {path}."
            )
        spacing = SourceVoxelSpacing(
            (
                float(properties["spatial-calibration-y"]),
                float(properties["spatial-calibration-x"]),
            )
        )
        x_site, y_site = float(properties["SiteX"]), float(properties["SiteY"])
        if (
            not x_site.is_integer()
            or not y_site.is_integer()
            or min(x_site, y_site) < 1
        ):
            raise ValueError(
                f"ImageXpress SiteX/Y must be positive integer coordinates in {path}."
            )
        if len(header.shape) != 2 or header.page_count != 1:
            raise ValueError(
                f"ImageXpress tile geometry requires a single 2D TIFF page in {path}."
            )
        geometry = SourceTileGeometry(
            x_pixels=float(properties["OffsetFromWellCenterUmX"])
            / spacing.values_zyx[-1],
            y_pixels=float(properties["OffsetFromWellCenterUmY"])
            / spacing.values_zyx[-2],
            row=int(y_site) - 1,
            column=int(x_site) - 1,
            width_pixels=int(header.shape[1]),
            height_pixels=int(header.shape[0]),
        )
        metadata = {SourceTileGeometry.metadata_field: geometry.as_metadata_value()}
        spacing.merge_into(metadata, path=str(path))
        OriginalSourceMetadata.from_mapping(
            {key: properties[key] for key in required}
        ).merge_into(
            metadata,
            path=str(path),
        )
        return metadata
