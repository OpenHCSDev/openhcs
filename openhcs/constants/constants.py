"""
Consolidated constants for OpenHCS.

This module defines all constants related to backends, defaults, I/O, memory, and pipeline.
These constants are governed by various doctrinal clauses.
"""

from enum import Enum
from typing import Set

from arraybridge.types import (
    CPU_MEMORY_TYPES as CPU_MEMORY_TYPES,
)
from arraybridge.types import (
    GPU_MEMORY_TYPES as GPU_MEMORY_TYPES,
)
from arraybridge.types import (
    MEMORY_TYPE_CUPY as MEMORY_TYPE_CUPY,
)
from arraybridge.types import (
    MEMORY_TYPE_JAX as MEMORY_TYPE_JAX,
)
from arraybridge.types import (
    MEMORY_TYPE_NUMPY as MEMORY_TYPE_NUMPY,
)
from arraybridge.types import (
    MEMORY_TYPE_PYCLESPERANTO as MEMORY_TYPE_PYCLESPERANTO,
)
from arraybridge.types import (
    MEMORY_TYPE_TENSORFLOW as MEMORY_TYPE_TENSORFLOW,
)
from arraybridge.types import (
    MEMORY_TYPE_TORCH as MEMORY_TYPE_TORCH,
)
from arraybridge.types import (
    SUPPORTED_MEMORY_TYPES as SUPPORTED_MEMORY_TYPES,
)
from arraybridge.types import (
    VALID_GPU_MEMORY_TYPES as VALID_GPU_MEMORY_TYPES,
)
from arraybridge.types import (
    VALID_MEMORY_TYPES as VALID_MEMORY_TYPES,
)
from arraybridge.types import (
    MemoryType as MemoryType,
)
from polystore.constants import Backend


class OrchestratorState(Enum):
    """Simple orchestrator state tracking - no complex state machine."""

    has_completed_initialization: bool
    skips_initialization: bool
    allows_execution: bool
    status_prefix: str

    CREATED = ("created", False, False, False, "")  # Object exists, not initialized
    READY = ("ready", True, True, False, "✓ Init")  # Initialized, ready for compilation
    COMPILED = ("compiled", True, True, True, "✓ Compiled")  # Compilation complete
    EXECUTING = (
        "executing",
        True,
        False,
        False,
        "🔄 Executing",
    )  # Execution in progress
    COMPLETED = (
        "completed",
        True,
        True,
        True,
        "✅ Complete",
    )  # Execution completed successfully
    INIT_FAILED = (
        "init_failed",
        False,
        False,
        False,
        "❌ Init Failed",
    )  # Initialization failed
    COMPILE_FAILED = (
        "compile_failed",
        True,
        False,
        False,
        "❌ Compile Failed",
    )  # Compilation failed
    EXEC_FAILED = (
        "exec_failed",
        True,
        False,
        False,
        "❌ Exec Failed",
    )  # Execution failed

    def __new__(
        cls,
        value: str,
        has_completed_initialization: bool,
        skips_initialization: bool,
        allows_execution: bool,
        status_prefix: str,
    ):
        obj = object.__new__(cls)
        obj._value_ = value
        obj.has_completed_initialization = has_completed_initialization
        obj.skips_initialization = skips_initialization
        obj.allows_execution = allows_execution
        obj.status_prefix = status_prefix
        return obj


# I/O-related constants
_TIFF_IMAGE_EXTENSIONS: Set[str] = {".tif", ".tiff"}
_RASTER_IMAGE_EXTENSIONS: Set[str] = {
    ".bmp",
    ".gif",
    ".jpeg",
    ".jpg",
    ".png",
}
DEFAULT_IMAGE_EXTENSIONS: Set[str] = set(_TIFF_IMAGE_EXTENSIONS)
LOADABLE_IMAGE_EXTENSIONS: Set[str] = _TIFF_IMAGE_EXTENSIONS | _RASTER_IMAGE_EXTENSIONS


class FileFormat(Enum):
    TIFF = list(DEFAULT_IMAGE_EXTENSIONS)
    NUMPY = [".npy"]
    TORCH = [".pt", ".torch", ".pth"]
    JAX = [".jax"]
    CUPY = [".cupy", ".craw"]
    TENSORFLOW = [".tf"]
    JSON = [".json"]
    CSV = [".csv"]
    TEXT = [".txt", ".py", ".md", ".swc"]
    ROI = [".roi.zip"]


DEFAULT_BACKEND = Backend.MEMORY
REQUIRES_DISK_READ = "requires_disk_read"
REQUIRES_DISK_WRITE = "requires_disk_write"
FORCE_DISK_WRITE = "force_disk_write"
READ_BACKEND = "read_backend"
WRITE_BACKEND = "write_backend"

