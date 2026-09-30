"""Synthetic identity-plus-three contract; no file IO or biological semantics."""

from openhcs.core.memory import numpy


@numpy
def registration_live_probe(image, offset=3):
    return image + offset
