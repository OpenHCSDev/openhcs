"""Bounded, read-only measurements of independently specified native geometry.

Pixel centres use source-native (y,x) coordinates. World geometry is the actual
Napari data_to_world transform, not a claim of verified physical calibration.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from math import ceil, floor, hypot, isfinite, pi, sqrt

import numpy as np
from skimage.measure import grid_points_in_poly, profile_line, regionprops

from openhcs.runtime.viewer_controls import (
    VerticesYX,
    ViewerIntensityStatistics,
    ViewerPolylineMeasurement,
    ViewerRegionMeasurement,
    ViewerPolygonGeometry,
    ViewerRasterRegionGeometry,
    ViewerPolylineControlOptions,
    ViewerRegionControlOptions,
)


@dataclass(frozen=True, slots=True)
class NativeMeasurementWindow:
    """A validated bounded source window; slicing/allocations happen afterwards."""

    y0: int
    x0: int
    y1: int
    x1: int

    @property
    def pixels(self) -> int:
        return (self.y1 - self.y0) * (self.x1 - self.x0)

    @classmethod
    def for_vertices(
        cls,
        vertices: VerticesYX,
        origin: tuple[int, int],
        shape: tuple[int, int],
        max_pixels: int,
    ) -> NativeMeasurementWindow:
        lower = tuple(min(v[a] for v in vertices) for a in range(2))
        upper = tuple(max(v[a] for v in vertices) for a in range(2))
        for axis in range(2):
            if (
                lower[axis] < origin[axis]
                or upper[axis] > origin[axis] + shape[axis] - 1
            ):
                raise ValueError(
                    "Measurement geometry is outside real source pixels (padding/out-of-bounds)."
                )
        window = cls(
            floor(lower[0]) - origin[0],
            floor(lower[1]) - origin[1],
            ceil(upper[0]) - origin[0] + 1,
            ceil(upper[1]) - origin[1] + 1,
        )
        if window.pixels > max_pixels:
            raise ValueError(
                "Measurement window exceeds max_pixels before reading/interpolating pixels."
            )
        return window

    def read(self, data: np.ndarray) -> np.ndarray:
        pixels = data[self.y0 : self.y1, self.x0 : self.x1]
        if not np.isfinite(pixels).all():
            raise ValueError("Measurement source window contains nonfinite pixels.")
        return pixels.astype(np.float64, copy=True)


@dataclass(frozen=True, slots=True)
class NativeImageMeasurement:
    """One accepted original 2D payload plus native transform; never display padding."""

    data: np.ndarray
    origin_yx: tuple[int, int]
    data_to_world: Callable[[tuple[float, float]], tuple[float, ...]]

    def __post_init__(self) -> None:
        if not isinstance(self.data, np.ndarray) or self.data.ndim != 2:
            raise ValueError(
                "Feature measurement requires one scalar native 2D image plane."
            )
        if self.data.dtype.kind not in "biuf":
            raise TypeError("Feature measurement requires real numeric pixels.")
        if len(self.origin_yx) != 2 or any(
            isinstance(v, bool) or not isinstance(v, int) or v < 0
            for v in self.origin_yx
        ):
            raise ValueError(
                "Measurement source origin must be two nonnegative integer indices."
            )
        if min(self.data.shape) <= 0:
            raise ValueError("Measurement requires nonempty source pixels.")

    def world_vertices(self, vertices: VerticesYX) -> tuple[tuple[float, ...], ...]:
        result = tuple(
            tuple(float(v) for v in self.data_to_world(point)) for point in vertices
        )
        if any(not all(isfinite(v) for v in point) for point in result):
            raise ValueError("Measurement native world transform is nonfinite.")
        return result

    @staticmethod
    def lengths(vertices: tuple[tuple[float, ...], ...]) -> tuple[float, ...]:
        return tuple(
            hypot(*(b - a for a, b in zip(start, end, strict=True)))
            for start, end in zip(vertices, vertices[1:])
        )

    def polyline(
        self, request: ViewerPolylineControlOptions
    ) -> ViewerPolylineMeasurement:
        vertices = request.vertices_yx
        lengths = self.lengths(vertices)
        if any(length == 0 or not isfinite(length) for length in lengths):
            raise ValueError("Polyline segments must have finite nonzero length.")
        counts = tuple(ceil(length + 1) for length in lengths)
        if (
            sum(counts) - len(counts) + 1 > request.max_samples
            or sum(counts) * request.line_width > 131072
        ):
            raise ValueError(
                "Polyline exceeds sample/work budget before interpolation."
            )
        windows = []
        for start, end, length in zip(
            vertices[:-1], vertices[1:], lengths, strict=True
        ):
            half = (request.line_width - 1) / 2
            normal = (
                -(end[1] - start[1]) * half / length,
                (end[0] - start[0]) * half / length,
            )
            corners = tuple(
                (v[0] + sign * normal[0], v[1] + sign * normal[1])
                for v in (start, end)
                for sign in (-1, 1)
            )
            windows.append(
                NativeMeasurementWindow.for_vertices(
                    corners, self.origin_yx, self.data.shape, request.max_pixels
                )
            )
        if sum(w.pixels for w in windows) > request.max_pixels:
            raise ValueError(
                "Polyline total source-window budget exceeded before reading pixels."
            )
        world = self.world_vertices(vertices)
        world_lengths = self.lengths(world)
        if any(
            length <= 0 or not isfinite(length) for length in world_lengths
        ) or not isfinite(sum(world_lengths)):
            raise ValueError("Native transform collapses or overflows the polyline.")
        profiles, data_distances, world_distances = [], [], []
        data_offset = world_offset = 0.0
        for i, (start, end, length, world_length, window) in enumerate(
            zip(
                vertices[:-1],
                vertices[1:],
                lengths,
                world_lengths,
                windows,
                strict=True,
            )
        ):
            pixels = window.read(self.data)
            local = tuple(
                (
                    v[0] - self.origin_yx[0] - window.y0,
                    v[1] - self.origin_yx[1] - window.x0,
                )
                for v in (start, end)
            )
            profile = profile_line(
                pixels,
                *local,
                linewidth=request.line_width,
                order=request.interpolation_order,
                mode="constant",
                cval=0.0,
                reduce_func=np.mean,
            )
            if len(profile) != counts[i] or not np.isfinite(profile).all():
                raise ValueError(
                    "Profile interpolation did not retain the accepted finite source support."
                )
            drop = 0 if i == 0 else 1
            profiles.extend(float(v) for v in profile[drop:])
            data_distances.extend(
                float(v)
                for v in (data_offset + np.linspace(0, length, counts[i]))[drop:]
            )
            world_distances.extend(
                float(v)
                for v in (world_offset + np.linspace(0, world_length, counts[i]))[drop:]
            )
            data_offset += length
            world_offset += world_length
        return ViewerPolylineMeasurement(
            vertices,
            world,
            sum(lengths),
            hypot(*(b - a for a, b in zip(vertices[0], vertices[-1]))),
            sum(world_lengths),
            hypot(*(b - a for a, b in zip(world[0], world[-1]))),
            tuple(data_distances),
            tuple(world_distances),
            tuple(profiles),
            ViewerIntensityStatistics.from_pixels(np.asarray(profiles)),
            request.line_width,
            request.interpolation_order,
        )

    @staticmethod
    def polygon_geometry(vertices: VerticesYX) -> ViewerPolygonGeometry:
        if len(set(vertices)) != len(vertices):
            raise ValueError("Polygon vertices must be distinct (closure is implicit).")
        # Simple polygons only: reject intersecting/touching non-adjacent edges.
        edges = tuple(zip(vertices, (*vertices[1:], vertices[0])))

        def cross(a, b, c):
            return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])

        def on(a, b, c):
            return cross(a, b, c) == 0 and all(
                min(x, y) <= z <= max(x, y) for x, y, z in zip(a, b, c)
            )

        for i, (a, b) in enumerate(edges):
            for j, (c, d) in enumerate(edges):
                if j <= i + 1 or (i == 0 and j == len(edges) - 1):
                    continue
                if (
                    cross(a, b, c) * cross(a, b, d) < 0
                    and cross(c, d, a) * cross(c, d, b) < 0
                ) or any((on(a, b, c), on(a, b, d), on(c, d, a), on(c, d, b))):
                    raise ValueError(
                        "Region polygon must be simple and non-self-intersecting."
                    )
        area = abs(sum(a[1] * b[0] - b[1] * a[0] for a, b in edges)) / 2
        perimeter = sum(hypot(b[0] - a[0], b[1] - a[1]) for a, b in edges)
        bbox_area = (max(v[0] for v in vertices) - min(v[0] for v in vertices)) * (
            max(v[1] for v in vertices) - min(v[1] for v in vertices)
        )
        if not isfinite(area) or area <= 0 or not isfinite(perimeter):
            raise ValueError(
                "Region polygon must have finite positive area and perimeter."
            )
        return ViewerPolygonGeometry(
            area, perimeter, area / bbox_area, 4 * pi * area / perimeter**2
        )

    def region(self, request: ViewerRegionControlOptions) -> ViewerRegionMeasurement:
        polygons = (
            (request.vertices_yx,)
            if request.background_vertices_yx is None
            else (request.vertices_yx, request.background_vertices_yx)
        )
        geometries = tuple(self.polygon_geometry(v) for v in polygons)
        windows = tuple(
            NativeMeasurementWindow.for_vertices(
                v, self.origin_yx, self.data.shape, request.max_pixels
            )
            for v in polygons
        )
        if (
            sum(w.pixels for w in windows) > request.max_pixels
            or sum(w.pixels * len(v) for w, v in zip(windows, polygons)) > 1048576
        ):
            raise ValueError(
                "Region total pixel/work budget exceeded before rasterization."
            )
        world = self.world_vertices(request.vertices_yx)
        basis = self.world_vertices(((0.0, 0.0), (1.0, 0.0), (0.0, 1.0)))
        y = np.subtract(basis[1], basis[0])
        x = np.subtract(basis[2], basis[0])
        determinant = float(np.dot(y, y) * np.dot(x, x) - np.dot(y, x) ** 2)
        if not isfinite(determinant) or determinant <= 0:
            raise ValueError("Native transform collapses the region plane.")
        world_area = geometries[0].area * sqrt(determinant)
        world_perimeter = sum(self.lengths((*world, world[0])))
        if (
            not isfinite(world_area)
            or not isfinite(world_perimeter)
            or world_perimeter <= 0
        ):
            raise ValueError("Native transform overflows the region geometry.")
        samples = []
        for vertices, window in zip(polygons, windows):
            local = (
                np.asarray(vertices)
                - np.asarray(self.origin_yx)
                - [window.y0, window.x0]
            )
            mask = grid_points_in_poly(
                (window.y1 - window.y0, window.x1 - window.x0), local
            )
            pixels = window.read(self.data)
            statistics = ViewerIntensityStatistics.from_pixels(pixels[mask])
            samples.append((mask, pixels, statistics))
        if len(samples) == 2:
            a, b = windows
            y0, x0 = max(a.y0, b.y0), max(a.x0, b.x0)
            y1, x1 = min(a.y1, b.y1), min(a.x1, b.x1)
            if (
                y0 < y1
                and x0 < x1
                and np.any(
                    samples[0][0][y0 - a.y0 : y1 - a.y0, x0 - a.x0 : x1 - a.x0]
                    & samples[1][0][y0 - b.y0 : y1 - b.y0, x0 - b.x0 : x1 - b.x0]
                )
            ):
                raise ValueError(
                    "Foreground and independently specified background pixels overlap."
                )
        mask, pixels, statistics = samples[0]
        region = regionprops(mask.astype(np.uint8), cache=False)[0]
        a = windows[0]
        perimeter = float(region.perimeter)
        raster = ViewerRasterRegionGeometry(
            int(region.area),
            (
                region.bbox[0] + a.y0 + self.origin_yx[0],
                region.bbox[1] + a.x0 + self.origin_yx[1],
                region.bbox[2] + a.y0 + self.origin_yx[0],
                region.bbox[3] + a.x0 + self.origin_yx[1],
            ),
            (
                region.centroid[0] + a.y0 + self.origin_yx[0],
                region.centroid[1] + a.x0 + self.origin_yx[1],
            ),
            float(region.extent),
            perimeter,
            4 * pi * region.area / perimeter**2 if perimeter > 0 else None,
            float(region.eccentricity),
        )
        background = samples[1][2] if len(samples) == 2 else None
        threshold = request.support_threshold
        if threshold is None and background is not None:
            threshold = (
                background.mean
                + request.background_sigma * background.standard_deviation
            )
        if threshold is not None and not isfinite(threshold):
            raise ValueError("Background support threshold overflowed.")
        support_count = (
            int(np.count_nonzero(pixels[mask] > threshold))
            if threshold is not None
            else None
        )
        return ViewerRegionMeasurement(
            request.vertices_yx,
            world,
            geometries[0],
            world_area,
            world_perimeter,
            4 * pi * world_area / world_perimeter**2,
            raster,
            statistics,
            request.background_vertices_yx,
            background,
            threshold,
            support_count,
            support_count / statistics.count if support_count is not None else None,
            statistics.mean - background.mean if background is not None else None,
            request.background_sigma,
        )
