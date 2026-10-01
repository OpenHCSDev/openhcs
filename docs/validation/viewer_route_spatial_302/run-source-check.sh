#!/bin/sh
set -eu
cd /home/ts/wt/openhcs-viewer-route-spatial-302-20260930
exec sh docs/validation/viewer_route_spatial_302/run-candidate.sh -c '
import openhcs
import pytest
raise SystemExit(pytest.main([
    "--noconftest", "-p", "no:cacheprovider", "-p", "pytestqt.plugin",
    "-o", "addopts=", "-q",
    "tests/unit/test_napari_streaming_handlers.py",
    "tests/unit/test_napari_accepted_work_settlement.py",
    "tests/unit/test_microscope_virtual_workspace_metadata.py",
    "tests/unit/test_acquisition_calibration_pipeline_journey.py",
    "tests/unit/test_template_crop_pipeline_execution.py",
    "--basetemp=/home/ts/.cache/agent-scratch/vr302/combined",
]))
'
