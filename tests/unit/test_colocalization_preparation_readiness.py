"""Canonical colocalization calls do not compile or load kernels after READY."""

import os
from pathlib import Path
import subprocess
import sys
import textwrap


def test_public_preparation_covers_canonical_metric_states_and_scopes(tmp_path):
    script = textwrap.dedent("""
        from unittest.mock import patch
        import numpy as np
        from numba.core.caching import Cache
        from numba.core.dispatcher import Dispatcher
        from openhcs.core.callable_contract import (
            CallableContract, CallableProjection, prepare_processing_callable,
        )
        from openhcs.core.runtime_image_values import ImagePayloadMetadata, image_payload_data
        from openhcs.processing.backends.cellprofiler import colocalization as module

        for process in (module.measure_colocalization, module.measure_colocalization_objects):
            for target in CallableProjection.from_callable(process).prepare_targets():
                prepare_processing_callable(target)
        object_call = CallableContract.from_callable(
            module.measure_colocalization_objects
        ).resolve_raw_runtime_callable()
        image_call = CallableContract.from_callable(
            module.measure_colocalization
        ).resolve_raw_runtime_callable()
        first = np.linspace(0.05, 0.95, 36, dtype=np.float32).reshape(6, 6)
        second = np.flip(first).copy()
        original_image = np.stack((first, second))
        image = ImagePayloadMetadata(source_channel_axis=0).payload_with(original_image.copy())
        labels = np.repeat(np.arange(1, 5, dtype=np.int32), 9).reshape(6, 6)
        original_labels = labels.copy()

        def reject_late_work(*args, **kwargs):
            raise AssertionError('Kernel compiled or loaded after public preparation')

        with patch.object(Dispatcher, 'compile', reject_late_work), patch.object(
            Cache, 'load_overload', reject_late_work
        ):
            for threshold_metrics in (False, True):
                for do_costes in (False, True):
                    options = dict(
                        threshold_percent=20.0,
                        do_correlation=True,
                        do_manders=threshold_metrics,
                        do_rwc=threshold_metrics,
                        do_overlap=threshold_metrics,
                        do_costes=do_costes,
                        scale_max=255,
                    )
                    for scope in module.CellProfilerMeasurementTargetScope:
                        output, rows = object_call(
                            image, labels, measurement_scope=scope, **options
                        )
                        selection = scope.measurement_scope_selection
                        expected_rows = int(selection.includes(module.MeasurementScope.IMAGE)) + 4 * int(selection.includes(module.MeasurementScope.OBJECT))
                        assert rows.row_count() == expected_rows
                        np.testing.assert_array_equal(output.data, original_image[0:1])
                    output, rows = image_call(image, **options)
                    assert rows.row_count() == 1
                    np.testing.assert_array_equal(output.data, original_image[0:1])
            context = module._prepare_object_colocalization_context(
                image, labels, channel_1=0, channel_2=1,
                threshold_percent=20.0, do_correlation=True, do_manders=True,
                do_rwc=True, do_overlap=True, do_costes=False,
                costes_method=module.CostesMethod.FASTER, scale_max=255,
                costes_backend_provider=module.DEFAULT_CELLPROFILER_BACKEND_SELECTION,
                image_pair_context=None, object_label_context=None,
            )
            _, rows = module._measure_colocalization_objects_core(context)
            np.testing.assert_allclose(rows.columns['correlation'], -1.0, atol=1e-6)
        np.testing.assert_array_equal(image.data, original_image)
        np.testing.assert_array_equal(labels, original_labels)
    """)
    environment = os.environ.copy()
    environment.update(
        OPENHCS_CPU_ONLY="true", NUMBA_CACHE_DIR=str(tmp_path / "kernels"),
    )
    result = subprocess.run(
        (sys.executable, "-c", script), cwd=Path(__file__).parents[2],
        env=environment, check=False, capture_output=True, text=True, timeout=90,
    )
    assert result.returncode == 0, result.stdout + result.stderr
