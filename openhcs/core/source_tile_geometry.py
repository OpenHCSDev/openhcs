"""Source-projection proof of a shared acquisition layout across channels."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass

from polystore.source_tile_geometry import SourceTileGeometry

from openhcs.constants.constants import AllComponents
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_projection import SourceProjectionSet


@dataclass(frozen=True, slots=True)
class SourceTileLayout:
    """A per-well site layout shared by every selected channel.

    Site identities and shapes, not filename ordering, prove the common canvas.
    Shared sparse acquisitions remain sparse. No coordinates are synthesized.
    """

    channel_sites: Mapping[str, Mapping[str, SourceTileGeometry]]

    @property
    def sites(self) -> Mapping[str, SourceTileGeometry]:
        return next(iter(self.channel_sites.values()))

    @classmethod
    def from_projection_set(
        cls, projections: SourceProjectionSet
    ) -> tuple[SourceTileLayout, ...]:
        groups: dict[
            tuple[str, ...], dict[str, dict[str, SourceTileGeometry | None]]
        ] = {}
        spacing_by_group: dict[tuple[str, ...], set[SourceVoxelSpacing]] = {}
        for projection in projections.plane_projections:
            address = projection.address
            key = tuple(
                address.value_for(component)
                for component in AllComponents
                if component not in (AllComponents.SITE, AllComponents.CHANNEL)
            )
            channel = address.value_for(AllComponents.CHANNEL)
            site = address.value_for(AllComponents.SITE)
            geometry = SourceTileGeometry.from_source_metadata(
                projection.source_metadata
            )
            if geometry is not None:
                spacing_by_group.setdefault(key, set()).add(
                    SourceVoxelSpacing.from_source_metadata(projection.source_metadata)
                )
            sites = groups.setdefault(key, {}).setdefault(channel, {})
            if site in sites and sites[site] != geometry:
                raise ValueError(
                    f"Conflicting source tile geometry for well coordinates {key}, site {site}."
                )
            sites[site] = geometry
        layouts = []
        for key, channels in groups.items():
            maps = tuple(channels.values())
            if not any(
                geometry is not None for sites in maps for geometry in sites.values()
            ):
                continue
            if any(geometry is None for sites in maps for geometry in sites.values()):
                raise ValueError(
                    f"Partially declared source tile geometry for well coordinates {key}."
                )
            if any(sites != maps[0] for sites in maps[1:]):
                raise ValueError(
                    f"Paired channels require identical source site geometry and canvas for {key}."
                )
            if len(spacing_by_group[key]) != 1:
                raise ValueError(
                    f"Shared acquisition layout requires equal XY calibration across every source for {key}."
                )
            coordinates = tuple(
                (geometry.x_pixels, geometry.y_pixels) for geometry in maps[0].values()
            )
            if len(coordinates) != len(set(coordinates)):
                raise ValueError(
                    f"Different source sites share one acquisition position for {key}."
                )
            layouts.append(cls(channel_sites=channels))
        return tuple(layouts)

    def row_major_grid_dimensions(self) -> tuple[int, int] | None:
        dimensions = []
        for sites in self.channel_sites.values():
            if not all(site.isdecimal() for site in sites) or tuple(sites) != tuple(
                sorted(sites, key=int)
            ):
                return None
            dimension = SourceTileGeometry.rectangular_grid_dimensions(
                sites.values(), require_row_major=True
            )
            if dimension is None:
                return None
            dimensions.append(dimension)
        return (
            dimensions[0]
            if dimensions and all(value == dimensions[0] for value in dimensions)
            else None
        )

    @classmethod
    def metadata_grid_dimensions(cls, projections: SourceProjectionSet) -> list[int]:
        layouts = cls.from_projection_set(projections)
        if not layouts or any(
            SourceTileGeometry.from_source_metadata(projection.source_metadata) is None
            for projection in projections.plane_projections
        ):
            return []
        dimensions = tuple(layout.row_major_grid_dimensions() for layout in layouts)
        if dimensions[0] is None or any(value != dimensions[0] for value in dimensions):
            return []
        return list(dimensions[0])
