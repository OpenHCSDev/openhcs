"""
Component configuration framework for OpenHCS.

This module provides the foundational component configuration system
that is used by constants.py to dynamically create enums.
"""

from .framework import ComponentConfiguration, ComponentConfigurationFactory

__all__ = [
    "ComponentConfiguration",
    "ComponentConfigurationFactory",
]
