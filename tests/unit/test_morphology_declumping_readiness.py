"""Library preparation must cover canonical image signatures before invocation."""

import os
from pathlib import Path
import subprocess
import sys
import textwrap


def test_declumping_preparation_rejects_late_compilation_or_disk_load(tmp_path):
    script = textwrap.dedent("""
        from contextlib import ExitStack
        from unittest.mock import patch
        import numpy as np
        from openhcs.core.callable_contract import prepare_processing_callable
        from openhcs.processing.backends.cellprofiler import morphology

        kernels = (
            morphology._smooth_image_for_declumping_numba,
            morphology._smooth_image_for_declumping_full_mask_numba,
        )
        assert all(not kernel.signatures for kernel in kernels)
        prepare_processing_callable(morphology.erode_objects)
        signatures = tuple(tuple(kernel.signatures) for kernel in kernels)
        assert all(signatures)

        def reject_late_preparation(signature):
            raise AssertionError(f'Late declumping compilation or cache load: {signature}')

        accelerated = morphology.NumbaNumpyMorphologyBackendStrategy()
        reference = morphology.NumpyMorphologyBackendStrategy()
        with ExitStack() as stack:
            for kernel in kernels:
                stack.enter_context(patch.object(kernel, 'compile', reject_late_preparation))
            for dtype in (np.float32, np.float64):
                for layout in ('C', 'F', 'strided'):
                    for readonly_image in (False, True):
                        image = np.arange(120, dtype=dtype).reshape(10, 12) / dtype(120)
                        image = np.array(image, order='F' if layout == 'F' else 'C')
                        if layout == 'strided':
                            image = image[::-1, ::-1]
                        image.flags.writeable = not readonly_image
                        for full_mask in (False, True):
                            for readonly_mask in (False, True):
                                mask = np.ones(image.shape, dtype=np.bool_)
                                if not full_mask:
                                    mask[:, :2] = False
                                mask.flags.writeable = not readonly_mask
                                before_image, before_mask = image.copy(), mask.copy()
                                expected = reference.smooth_image_for_declumping(image, mask, 3.0)
                                actual = accelerated.smooth_image_for_declumping(image, mask, 3.0)
                                np.testing.assert_allclose(actual, expected, rtol=1e-12, atol=1e-12)
                                assert actual.dtype == image.dtype
                                assert not np.shares_memory(actual, image)
                                np.testing.assert_array_equal(image, before_image)
                                np.testing.assert_array_equal(mask, before_mask)
        assert tuple(tuple(kernel.signatures) for kernel in kernels) == signatures
    """)
    environment = os.environ.copy()
    environment.update(
        OPENHCS_CPU_ONLY="true", NUMBA_CACHE_DIR=str(tmp_path / "kernels"),
        PYTHONDONTWRITEBYTECODE="1",
    )
    # The second fresh interpreter must load its prepared signatures before the
    # same refusal gate; a populated disk cache does not count as READY.
    for _ in range(2):
        result = subprocess.run(
            (sys.executable, "-c", script), cwd=Path(__file__).parents[2],
            env=environment, capture_output=True, text=True, timeout=160,
        )
        assert result.returncode == 0, result.stdout + result.stderr
