"""Native-coordinate presentation of frozen images, labels and graph paths."""

import json
from abc import ABC, abstractmethod
from pathlib import Path

import numpy as np
import tifffile
from matplotlib.colors import hsv_to_rgb
from matplotlib.patheffects import withStroke
from build_slas_agent import digest, nonempty_label_plane

BRIGHT_OBJECT_SOURCE = Path("paper/figures/slas/frozen_bright_object_views.json")
NUCLEAR_SOURCE = Path("paper/figures/slas/frozen_nuclear_views.json")
RETINAL_SOURCE = Path("paper/figures/slas/frozen_retinal_views.json")


class FrozenImageView(ABC):
    """Draw retained pixels and detections without executing an analysis."""

    raw_cmap = "gray"
    overlay_opacity = .75
    units_per_pixel = 1
    scale_unit = "px"
    pixel_aspect = 1

    def __init__(self, sheet, declaration):
        self.sheet = sheet
        sheet.source(Path(__file__).resolve())
        self.declaration = declaration
        root = sheet.input_path(Path(declaration["root"]))
        self.paths = {}
        for role, source in declaration["files"].items():
            path = self.checked_path(root, source)
            self.paths[role] = path
            sheet.source(path)
        self.raw = self.read_raw(self.paths["raw"])
        self.labels = self.read_labels(self.label_path)
        if self.raw.ndim != 2 or self.raw.shape != self.labels.shape:
            raise ValueError("Frozen raw field and label plane must match")
        sheet.display_transforms.append({
            "author_run": declaration["author_run"], "attempt": declaration["attempt"],
            "operation": "Frozen arrays in native coordinates; categorical label colours",
            "source_shape_yx": list(self.raw.shape), "raw_window": self.window,
            "region_yyxx": list(self.region), "raw_cmap": self.raw_cmap,
            "overlay_opacity": self.overlay_opacity,
            "units_per_pixel": self.units_per_pixel, "scale_unit": self.scale_unit,
            "pixel_aspect": self.pixel_aspect,
            "gamma": 1, "analysis_rerun": False,
        })

    @property
    def viewport(self):
        return self.declaration

    @property
    def window(self):
        return self.viewport["raw_window"]

    @property
    @abstractmethod
    def label_path(self):
        """The member's saved primary detections, already hash-checked."""
        raise NotImplementedError

    def read_raw(self, path):
        return tifffile.imread(path)

    def read_labels(self, path):
        return nonempty_label_plane(path)

    @staticmethod
    def checked_path(root, source):
        path = root / source["path"]
        if digest(path) != source["sha256"]:
            raise ValueError(f"Frozen image source changed: {path}")
        return path

    @property
    def region(self):
        height, width = self.raw.shape
        return 0, height, 0, width

    @staticmethod
    def colour(labels):
        hues = np.mod(np.asarray(labels) * 0.618033988749895, 1)
        return hsv_to_rgb(np.stack((hues, np.full_like(hues, .75),
                                   np.full_like(hues, .65)), axis=-1))

    def axis(self, bounds):
        x, y, width, height = bounds
        axis = self.sheet.figure.add_axes((x / 100, y / 100, width / 100, height / 100))
        top, bottom, left, right = self.region
        height_px, width_px = bottom - top, right - left
        width_units = width_px * self.units_per_pixel
        magnitude = 10 ** np.floor(np.log10(width_units / 5))
        length_units = np.floor(width_units / 5 / magnitude) * magnitude
        length_px = length_units / self.units_per_pixel
        bar_left, bar_bottom = left + width_px * .05, bottom - height_px * .05
        bar, = axis.plot((bar_left, bar_left + length_px), (bar_bottom, bar_bottom),
                         color="black", linewidth=2, zorder=10)
        bar.set_path_effects([withStroke(linewidth=4, foreground="white")])
        axis.text(bar_left, bar_bottom - height_px * .025,
                  f"{length_units:g} {self.scale_unit}", ha="left", va="bottom",
                  fontsize=self.sheet.plot_font_size, color="black", zorder=10,
                  bbox={"facecolor": "white", "edgecolor": "none", "alpha": .9, "pad": 1})
        axis.set(xlim=(left-.5, right-.5), ylim=(bottom-.5, top-.5))
        axis.set_axis_off()
        return axis

    def paint_raw(self, axis):
        axis.imshow(self.raw, cmap=self.raw_cmap, vmin=self.window[0],
                    vmax=self.window[1], interpolation="nearest", aspect=self.pixel_aspect)

    def paint_result(self, axis, labels, opacity):
        rgba = np.zeros((*labels.shape, 4), dtype=np.float32)
        rgba[..., :3] = self.colour(labels)
        rgba[..., 3] = (labels != 0) * opacity
        axis.imshow(rgba, interpolation="nearest", aspect=self.pixel_aspect)

    def draw_raw(self, bounds):
        self.paint_raw(self.axis(bounds))

    def draw_result(self, bounds):
        self.paint_result(self.axis(bounds), self.labels, 1)

    def paint_overlay(self, axis, labels):
        self.paint_raw(axis)
        self.paint_result(axis, labels, self.overlay_opacity)

    def draw_overlay(self, bounds):
        self.paint_overlay(self.axis(bounds), self.labels)


class CroppedImageView(FrozenImageView):
    """An explicitly recorded region of the original array, in pixel units."""

    @property
    def region(self):
        top, bottom, left, right = self.viewport["region_yyxx"]
        height, width = self.raw.shape
        if not (0 <= top < bottom <= height and 0 <= left < right <= width):
            raise ValueError("Frozen image region lies outside its original array")
        return top, bottom, left, right


class FrozenComparison(FrozenImageView):
    """First and final saved detections share one raw image and native region."""

    @classmethod
    def read(cls, sheet, receipt, view_index=0):
        path = sheet.input_path(receipt)
        sheet.source(path)
        return cls(sheet, json.loads(path.read_text()), view_index)

    def __init__(self, sheet, declaration, view_index=0):
        self.view_index = view_index
        super().__init__(sheet, declaration)
        self.final_labels = self.read_labels(self.paths["final"])
        if self.raw.shape != self.final_labels.shape:
            raise ValueError("Final detections must match the comparison's raw image")

    @property
    def viewport(self):
        return self.declaration["views"][self.view_index]

    @property
    def label_path(self):
        return self.paths["first"]

    @property
    def overlay_opacity(self):
        return self.declaration["overlay_opacity"]

    def draw_final(self, bounds):
        self.paint_overlay(self.axis(bounds), self.final_labels)

    def draw_final_result(self, bounds):
        self.paint_result(self.axis(bounds), self.final_labels, 1)

    def draw_row(self, bounds, heading_y):
        self.draw_columns(bounds, heading_y, (
            ("Raw", self.draw_raw), ("First result", self.draw_overlay),
            ("Final result", self.draw_final),
        ))

    def draw_final_row(self, bounds, heading_y):
        self.draw_columns(bounds, heading_y, (
            ("Raw", self.draw_raw), ("Final labels", self.draw_final_result),
            ("Overlay", self.draw_final),
        ))

    def draw_columns(self, bounds, heading_y, panels):
        x, y, width, height = bounds
        gap = width * .02
        column_width = (width - (len(panels) - 1) * gap) / len(panels)
        for column, (heading, draw) in enumerate(panels):
            left = x + column * (column_width + gap)
            self.sheet.text(left, heading_y, heading,
                            size=self.sheet.plot_font_size, weight="bold")
            draw((left, y, column_width, height))


class CroppedComparison(CroppedImageView, FrozenComparison):
    """Compose a matched first/final comparison with a recorded native region."""


class BioFormatsImageView(FrozenImageView):
    """Decode the raw plane and its physical scale through the existing owner."""

    scale_unit = "µm"

    def read_raw(self, path):
        from polystore.bioformats_java import BioFormatsJavaContext, load_bioformats_plane

        context = BioFormatsJavaContext.instance()
        series = self.declaration["series_index"]
        opened = context.open_reader(path)
        try:
            units = context.scyjava.jimport("ome.units.UNITS")
            x = float(opened.metadata.getPixelsPhysicalSizeX(series).value(units.MICROMETER))
            y = float(opened.metadata.getPixelsPhysicalSizeY(series).value(units.MICROMETER))
            if not (x > 0 and y > 0):
                raise ValueError("Original image must declare positive physical pixel sizes")
            self.units_per_pixel = x
            self.pixel_aspect = y / x
        finally:
            opened.close()
        return load_bioformats_plane(source_path=path, series_index=series,
                                     plane_index=self.declaration["plane_index"])


class BioFormatsComparison(BioFormatsImageView, CroppedComparison):
    """Compose physical raw-plane decoding with matched cropped detections."""


class FrozenNeuriteView(FrozenImageView):
    """Retained cell-body labels plus their authoritative graph paths."""

    raw_cmap = "gray_r"

    def __init__(self, sheet, declaration):
        from polystore.roi import load_rois_from_zip

        super().__init__(sheet, declaration)
        self.rois = load_rois_from_zip(self.paths["paths"])
        sheet.display_transforms.append({
            "author_run": declaration["author_run"], "attempt": declaration["attempt"],
            "operation": "Vector strokes from frozen neurite graph paths",
            "path_stroke_points": .55, "analysis_rerun": False,
        })

    @property
    def label_path(self):
        return self.paths["bodies"]

    def paint_result(self, axis, labels, opacity):
        super().paint_result(axis, labels, opacity)
        for roi in self.rois:
            colour = self.colour(int(roi.metadata["neuron_label"]))
            for shape in roi.shapes:
                coordinates = np.asarray(shape.coordinates)
                if coordinates.ndim != 2 or coordinates.shape[1] != 2:
                    raise ValueError("Figure requires the frozen 2-D graph projection")
                axis.plot(coordinates[:, 1], coordinates[:, 0],
                          color=colour, linewidth=.55)
