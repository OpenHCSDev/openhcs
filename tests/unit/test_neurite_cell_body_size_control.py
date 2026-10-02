"""Synthetic controls for the declared soma acceptance gate, not biology QA."""

from dataclasses import dataclass, replace

import numpy as np
import pytest

from openhcs.core.runtime_object_labels import object_label_dense_array
from openhcs.processing.backends.analysis.neurite_outgrowth import (
    CELLPROFILER_NEURITE_ENGINE_PROFILE,
    MetaXpressCellBodySettings,
    _identify_cell_bodies_cellprofiler,
    _identify_nuclear_seeded_cell_bodies_cellprofiler,
)


def _small_body_image():
    image = np.zeros((64, 64), dtype=np.uint16)
    image[28:35, 28:36] = 1200
    return image


def _small_body_contract(settings, calibration=1.3556):
    labels = (_small_body_image() > 0).astype(np.int32)
    return settings.contract_candidates(labels, _small_body_image(), calibration)


def test_default_gate_rejects_area_qualified_small_body_and_declared_gate_accepts():
    calibration = 1.3556
    settings = MetaXpressCellBodySettings(
        minimum_area=100.0,
        approximate_max_width=30.0,
        intensity_above_local_background=100.0,
    )
    assert 56 * calibration**2 > settings.minimum_area
    np.testing.assert_array_equal(_small_body_contract(settings), [False, False])
    smaller = replace(settings, minimum_inscribed_diameter_px=5.0)
    np.testing.assert_array_equal(_small_body_contract(smaller), [False, True])
    assert settings.minimum_inscribed_diameter_px == (
        CELLPROFILER_NEURITE_ENGINE_PROFILE.compact_body_min_diameter_px
    )


@pytest.mark.parametrize(
    "overrides",
    (
        {"minimum_area": 104.0},
        {"intensity_above_local_background": 1201.0},
        {"approximate_max_width": 5.0},
    ),
)
def test_smaller_gate_retains_area_intensity_and_upper_width_rejection(overrides):
    settings = MetaXpressCellBodySettings(
        minimum_inscribed_diameter_px=5.0,
        minimum_area=100.0,
        approximate_max_width=30.0,
        intensity_above_local_background=100.0,
    )
    np.testing.assert_array_equal(
        _small_body_contract(replace(settings, **overrides)), [False, False]
    )


def test_original_detector_defaults_equal_explicit_legacy_gate():
    settings = MetaXpressCellBodySettings(minimum_area=100.0)
    default = _identify_cell_bodies_cellprofiler(
        _small_body_image(), settings, 1.3556, bright_objects=True
    )
    explicit = _identify_cell_bodies_cellprofiler(
        _small_body_image(), replace(settings, minimum_inscribed_diameter_px=10.0),
        1.3556, bright_objects=True,
    )
    np.testing.assert_array_equal(
        object_label_dense_array(default), object_label_dense_array(explicit)
    )
    assert CELLPROFILER_NEURITE_ENGINE_PROFILE.compact_body_detection_kwargs(
        adaptive_window_size=32
    ) == CELLPROFILER_NEURITE_ENGINE_PROFILE.body_detection_kwargs(
        adaptive_window_size=32, exclude_size=False, min_diameter=10
    )


def test_gate_pixel_units_do_not_replace_area_calibration_and_zero_is_explicit():
    settings = MetaXpressCellBodySettings(
        minimum_inscribed_diameter_px=0.0, minimum_area=100.0
    )
    settings.validate()
    np.testing.assert_array_equal(_small_body_contract(settings), [False, True])
    np.testing.assert_array_equal(_small_body_contract(settings, 1.0), [False, False])


@pytest.mark.parametrize("nuclear_seeded", (False, True))
def test_independent_gate_audit_composes_through_original_detector_consumers(nuclear_seeded):
    gates = []

    class GateAudit:
        def contract_candidates(self, labels, response, pixel_size_um):
            gates.append(self.minimum_inscribed_diameter_px)
            return super().contract_candidates(labels, response, pixel_size_um)

    @dataclass(frozen=True)
    class AuditedBodySettings(GateAudit, MetaXpressCellBodySettings):
        """Audit contribution composes the original calibrated gate owner."""

    settings = AuditedBodySettings(minimum_inscribed_diameter_px=5.0)
    if nuclear_seeded:
        nuclei = np.zeros((64, 64), dtype=np.int32)
        nuclei[30:33, 30:33] = 1
        _identify_nuclear_seeded_cell_bodies_cellprofiler(
            _small_body_image(), settings, 1.3556, bright_objects=True,
            nuclei_labels=nuclei,
        )
        assert gates == [5.0, 5.0]
    else:
        _identify_cell_bodies_cellprofiler(
            _small_body_image(), settings, 1.3556, bright_objects=True
        )
        assert gates == [5.0]


@pytest.mark.parametrize("diameter", (-1.0, np.nan, np.inf))
def test_body_size_gate_requires_finite_nonnegative_pixel_units(diameter):
    settings = MetaXpressCellBodySettings(minimum_inscribed_diameter_px=diameter)
    with pytest.raises(ValueError, match="minimum_inscribed_diameter_px"):
        settings.validate()
