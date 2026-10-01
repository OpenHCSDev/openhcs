"""Declared warmup covers representative edge and integer-label runtime signatures."""

import os
import subprocess
import sys
import textwrap
from pathlib import Path


def test_declared_preparation_covers_sobel_and_integer_label_shrink(tmp_path):
    script = textwrap.dedent("""
        import numpy as np
        from openhcs.core.callable_contract import prepare_processing_callable
        from openhcs.processing.backends.cellprofiler.edge import (
            EdgeMethod, enhance_edges, _sobel_numba_kernel,
        )
        from openhcs.processing.backends.cellprofiler.morphology import (
            ShrinkDefinedPixelsStrategy, expand_or_shrink_objects,
            _binary_shrink_2d_numba,
        )
        assert not _sobel_numba_kernel.signatures
        assert not _binary_shrink_2d_numba.signatures
        prepare_processing_callable(enhance_edges)
        prepare_processing_callable(expand_or_shrink_objects)
        dispatchers = (_sobel_numba_kernel, _binary_shrink_2d_numba)
        before = tuple(tuple(dispatcher.signatures) for dispatcher in dispatchers)
        assert all(before)
        misses = tuple(sum(dispatcher.stats.cache_misses.values()) for dispatcher in dispatchers)
        image = np.arange(256, dtype=np.float32).reshape(16, 16)
        edges = enhance_edges.__wrapped__(image, method=EdgeMethod.SOBEL)
        labels = np.zeros((16, 16), dtype=np.int32)
        labels[2:7, 3:9] = 1
        shrunken = ShrinkDefinedPixelsStrategy().apply(labels, iterations=2, fill_holes=False)
        assert edges.shape == image.shape
        assert shrunken.dtype == np.int32
        assert np.any(shrunken) and np.count_nonzero(shrunken) < np.count_nonzero(labels)
        assert tuple(tuple(dispatcher.signatures) for dispatcher in dispatchers) == before
        assert tuple(sum(dispatcher.stats.cache_misses.values()) for dispatcher in dispatchers) == misses
    """)
    environment = os.environ.copy()
    environment.update(
        {"OPENHCS_CPU_ONLY": "true", "NUMBA_CACHE_DIR": str(tmp_path / "kernels")}
    )
    result = subprocess.run(
        (sys.executable, "-c", script),
        cwd=Path(__file__).parents[2],
        env=environment,
        check=False,
        capture_output=True,
        text=True,
        timeout=90,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_registry_preparation_covers_volume_erosion_and_quantized_diagnostics(tmp_path):
    script = textwrap.dedent("""
        from contextlib import ExitStack
        from unittest.mock import patch

        import numpy as np
        from numba.core.dispatcher import Dispatcher

        from openhcs.core.callable_contract import prepare_processing_callable
        from openhcs.processing.backends.cellprofiler.morphology import (
            NumbaNumpyMorphologyBackendStrategy,
            NumpyMorphologyBackendStrategy,
            _erode_labeled_objects_numba,
            erode_objects,
        )
        from openhcs.processing.backends.cellprofiler.thresholding import (
            NumbaNumpyThresholdDiagnosticsBackendStrategy,
            threshold,
        )
        from openhcs.processing.backends.cellprofiler.thresholding_threshold_numba_diagnostics_quantized import (
            _populate_quantized_threshold_codebook_numba,
            _threshold_diagnostics_rectangular_mask_quantized_numba,
            _threshold_diagnostics_unmasked_finite_quantized_numba,
        )

        dispatchers = (
            _erode_labeled_objects_numba,
            _populate_quantized_threshold_codebook_numba,
            _threshold_diagnostics_rectangular_mask_quantized_numba,
            _threshold_diagnostics_unmasked_finite_quantized_numba,
        )
        assert all(not dispatcher.signatures for dispatcher in dispatchers)
        prepare_processing_callable(erode_objects)
        prepare_processing_callable(threshold)
        before = tuple(tuple(dispatcher.signatures) for dispatcher in dispatchers)
        assert all(before)
        late = []
        original_compile = Dispatcher.compile

        def record_compile(dispatcher, signature):
            late.append((dispatcher.py_func.__name__, str(signature)))
            return original_compile(dispatcher, signature)

        morphology = NumbaNumpyMorphologyBackendStrategy()
        diagnostics = NumbaNumpyThresholdDiagnosticsBackendStrategy()
        with ExitStack() as stack:
            for dispatcher in dispatchers:
                stack.enter_context(patch.object(
                    dispatcher, "compile",
                    lambda signature, dispatcher=dispatcher: record_compile(dispatcher, signature),
                ))
            for shape in ((7, 8), (5, 7, 8)):
                labels = np.zeros(shape, dtype=np.int32)
                labels[..., 1:6, 1:7] = 1
                labels[..., 3:5, 4:7] = 2
                footprint = np.ones((3,) * labels.ndim, dtype=np.bool_)
                expected = NumpyMorphologyBackendStrategy().erode_labeled_objects(labels, footprint)
                np.testing.assert_array_equal(
                    morphology.erode_labeled_objects(labels, footprint), expected,
                )
            for producer_dtype in (np.float32, np.float64):
                for code_dtype in (np.uint8, np.uint16):
                    scale = int(np.iinfo(code_dtype).max)
                    codes = np.arange(36, dtype=code_dtype).reshape((6, 6)) * (scale // 36)
                    image = codes.astype(producer_dtype) / producer_dtype(scale)
                    binary = image > 0.5
                    partial_mask = np.ones(image.shape, dtype=np.bool_)
                    partial_mask[:, :2] = False
                    for mask in (None, partial_mask):
                        planar = diagnostics.diagnostics(
                            image, mask, binary, proven_unit_interval_scale=scale,
                        )
                        volume = diagnostics.diagnostics(
                            image[None, ...],
                            None if mask is None else mask[None, ...],
                            binary[None, ...], proven_unit_interval_scale=scale,
                        )
                        assert np.all(np.isfinite(planar)) and np.all(np.isfinite(volume))
        assert not late, late
        assert tuple(tuple(dispatcher.signatures) for dispatcher in dispatchers) == before
    """)
    environment = os.environ.copy()
    environment.update(
        {"OPENHCS_CPU_ONLY": "true", "NUMBA_CACHE_DIR": str(tmp_path / "kernels")}
    )
    result = subprocess.run(
        (sys.executable, "-c", script),
        cwd=Path(__file__).parents[2],
        env=environment,
        check=False,
        capture_output=True,
        text=True,
        timeout=120,
    )
    assert result.returncode == 0, result.stdout + result.stderr
