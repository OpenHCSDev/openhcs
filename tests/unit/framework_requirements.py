"""Declared optional array-framework requirements for tests."""

from __future__ import annotations

import importlib
from types import ModuleType

import pytest

from openhcs.constants import MemoryType


def requires_framework(memory_type: MemoryType) -> pytest.MarkDecorator:
    """Mark a test that needs one optional framework (an install extra)."""

    return pytest.mark.skipif(
        not memory_type.library.is_installed(),
        reason=f"requires the optional {memory_type.value} framework",
    )


def framework_module(memory_type: MemoryType, module_name: str) -> ModuleType:
    """Import a module that needs ``memory_type``, inside a marked test only."""

    if not memory_type.library.is_installed():
        raise AssertionError(
            f"{module_name} needs {memory_type.value}; mark the test with "
            f"requires_framework(MemoryType.{memory_type.name})."
        )
    return importlib.import_module(module_name)
