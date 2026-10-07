"""Full-resolution presentation of frozen arrays and authoritative graph paths."""

from pathlib import Path

import numpy as np
import tifffile
from matplotlib.colors import hsv_to_rgb
from polystore.roi import load_rois_from_zip

from build_slas_agent import digest, nonempty_label_plane


class FrozenNeuriteView:
    """One retained field, not a new segmentation or tracing method."""

    def __init__(self, sheet, declaration):
        root = Path(declaration["root"])
        paths = {}
        for role, source in declaration["files"].items():
            path = root / source["path"]
            if digest(path) != source["sha256"]:
                raise ValueError(f"Frozen neurite source changed: {path}")
            paths[role] = path
        self.raw = tifffile.imread(paths["raw"])
        self.bodies = nonempty_label_plane(paths["bodies"])
        self.rois = load_rois_from_zip(paths["paths"])
        if self.raw.ndim != 2 or self.raw.shape != self.bodies.shape:
            raise ValueError("Frozen raw field and body-label plane must match")
        self.window = declaration["raw_window"]
        self.sheet = sheet
        sheet.display_transforms.append({
            "author_run": declaration["author_run"], "attempt": declaration["attempt"],
            "operation": "Full-resolution frozen arrays; dark label colours and vector graph strokes; inverted raw display",
            "source_shape_yx": list(self.raw.shape), "raw_window": self.window,
            "gamma": 1, "path_stroke_points": 0.55,
            "analysis_rerun": False,
        })

    @staticmethod
    def colour(labels):
        hues = np.mod(np.asarray(labels) * 0.618033988749895, 1)
        return hsv_to_rgb(np.stack((hues, np.full_like(hues, .75),
                                   np.full_like(hues, .65)), axis=-1))

    def draw(self, bounds, *, raw=False, result=False):
        x, y, width, height = bounds
        axis = self.sheet.figure.add_axes((x / 100, y / 100, width / 100, height / 100))
        if raw:
            axis.imshow(self.raw, cmap="gray_r", vmin=self.window[0],
                        vmax=self.window[1], interpolation="nearest")
        if result:
            rgba = np.zeros((*self.bodies.shape, 4))
            rgba[..., :3] = self.colour(self.bodies)
            rgba[..., 3] = (self.bodies != 0) * (.75 if raw else 1)
            axis.imshow(rgba, interpolation="nearest")
            for roi in self.rois:
                colour = self.colour(int(roi.metadata["neuron_label"]))
                for shape in roi.shapes:
                    coordinates = np.asarray(shape.coordinates)
                    if coordinates.ndim != 2 or coordinates.shape[1] != 2:
                        raise ValueError("Figure requires the frozen 2-D graph projection")
                    axis.plot(coordinates[:, 1], coordinates[:, 0],
                              color=colour, linewidth=.55)
        height_px, width_px = self.raw.shape
        axis.set(xlim=(-.5, width_px-.5), ylim=(height_px-.5, -.5), aspect="equal")
        axis.set_axis_off()
