"""TEMPORARY (surface R1): record enclosing-circle inputs and results in every process.

Active only when R1_DEBUG_DUMP_DIR is set. Loaded through PYTHONPATH, so the
execution server and its workers record too. Deleted before the PR is final.
"""

import importlib.abc
import importlib.util
import os
import sys

_TARGET = "openhcs.processing.backends.cellprofiler.label_geometry"
_DUMP_DIR = os.environ.get("R1_DEBUG_DUMP_DIR", "")


def _instrument(module):
    import math
    import time

    import numpy as np

    arccos = module._numpy_124_arccos
    circle = module.minimum_enclosing_circle_from_labels
    calls = []

    def recording_arccos(values):
        result = arccos(values)
        calls.append((np.array(values, dtype=np.float64), np.array(result)))
        return result

    def recording_circle(labels, label_ids):
        del calls[:]
        centers, radii = circle(labels, label_ids)
        inputs = np.concatenate([c[0] for c in calls]) if calls else np.zeros(0)
        outputs = np.concatenate([c[1] for c in calls]) if calls else np.zeros(0)
        os.makedirs(_DUMP_DIR, exist_ok=True)
        np.savez_compressed(
            os.path.join(_DUMP_DIR, f"circle_{os.getpid()}_{time.time_ns()}.npz"),
            labels=np.asarray(labels),
            ids=np.asarray(label_ids),
            centers=centers,
            radii=radii,
            arccos_in=inputs,
            arccos_out=outputs,
            arccos_libm=np.array([math.acos(v) if -1 <= v <= 1 else np.nan for v in inputs]),
            arccos_numpy=np.arccos(inputs),
            svml=np.array(bool(module._NUMPY_124_SVML_ACOS_AVAILABLE)),
        )
        return centers, radii

    module._numpy_124_arccos = recording_arccos
    module.minimum_enclosing_circle_from_labels = recording_circle


def _recording_loader_type(loader_type):
    """The real loader's own type, instrumenting after it executes the module."""

    class RecordingLoader(loader_type):
        def exec_module(self, module):
            super().exec_module(module)
            _instrument(module)

    return RecordingLoader


class _Finder(importlib.abc.MetaPathFinder):
    def find_spec(self, name, path, target=None):
        if name != _TARGET:
            return None
        sys.meta_path.remove(self)
        try:
            spec = importlib.util.find_spec(name)
        finally:
            sys.meta_path.insert(0, self)
        if spec is not None and spec.loader is not None:
            spec.loader.__class__ = _recording_loader_type(type(spec.loader))
        return spec


if _DUMP_DIR:
    sys.meta_path.insert(0, _Finder())
