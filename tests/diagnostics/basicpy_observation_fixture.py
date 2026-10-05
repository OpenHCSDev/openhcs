"""Shared numerical acquisition controls; never blind microscopy inputs."""

import numpy as np


def shaded_observations(*, stationary_biology=False, volume=False):
    """Known shading with either moving objects or a confounded stationary pattern."""
    size = 32
    count = 24
    yy, xx = np.mgrid[-1 : 1 : complex(size), -1 : 1 : complex(size)]
    flatfield = 1.2 - 0.3 * (yy**2 + xx**2) + 0.1 * xx
    flatfield /= flatfield.mean()
    rng = np.random.default_rng(213)
    observations = []
    for index in range(count):
        background = 3000 + 50 * index
        if stationary_biology:
            # Successful convergence cannot separate stationary biology from shading.
            biology = background * np.exp(-((xx - 0.2) ** 2 + (yy + 0.1) ** 2) / 0.09)
        else:
            cx, cy = rng.uniform(-0.8, 0.8, size=2)
            biology = 5000 * np.exp(-((xx - cx) ** 2 + (yy - cy) ** 2) / 0.008)
        frame = (background + biology) * flatfield
        observations.append(np.rint(frame).astype(np.uint16))
    observations = np.stack(observations)
    if volume:
        observations = np.stack((observations, observations), axis=1)
        flatfield = np.stack((flatfield, flatfield))
    return observations, flatfield
