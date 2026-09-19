"""Lightweight image payload execution mode declaration.

A pure enum with no runtime imports, so declaration-only consumers
(callable contracts, function references, agent DTOs) do not pay the
NumPy import cost of the aligned image payload runtime module.
"""

from __future__ import annotations

from enum import Enum


class ImagePayloadExecutionMode(Enum):
    """How a runtime executor should interpret a resolved image payload."""

    NATURAL = "natural"
    FULL_STACK = "full_stack"
    ALIGNED_MULTI_IMAGE_STACK = "aligned_multi_image_stack"
