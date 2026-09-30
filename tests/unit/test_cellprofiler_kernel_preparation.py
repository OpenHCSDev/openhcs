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
