"""
Consolidated constants for OpenHCS.

This module defines all constants related to backends, defaults, I/O, memory, and pipeline.
These constants are governed by various doctrinal clauses.
"""

from enum import Enum
from abc import ABC
from typing import ClassVar, Set

from metaclass_registry import AutoRegisterMeta

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


class OrchestratorState(ABC, metaclass=AutoRegisterMeta):
    """One lifecycle state of a dataset's orchestrator.

    Each state is a subclass declaring what it allows; ``name`` is its spelling
    on the wire and in status text.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True

    name: ClassVar[str | None] = None
    has_completed_initialization: ClassVar[bool]
    skips_initialization: ClassVar[bool]
    allows_execution: ClassVar[bool]
    status_prefix: ClassVar[str]

    @staticmethod
    def named(name: str) -> type["OrchestratorState"] | None:
        """The state spelled ``name``, or ``None`` for an unknown spelling."""
        return OrchestratorState.__registry__.get(name)


class OrchestratorCreated(OrchestratorState):
    """The orchestrator exists and is not initialized."""

    name = "created"
    has_completed_initialization = False
    skips_initialization = False
    allows_execution = False
    status_prefix = ""


class OrchestratorReady(OrchestratorState):
    """Initialized and ready for compilation."""

    name = "ready"
    has_completed_initialization = True
    skips_initialization = True
    allows_execution = False
    status_prefix = "✓ Init"


class OrchestratorCompiled(OrchestratorState):
    name = "compiled"
    has_completed_initialization = True
    skips_initialization = True
    allows_execution = True
    status_prefix = "✓ Compiled"


class OrchestratorExecuting(OrchestratorState):
    name = "executing"
    has_completed_initialization = True
    skips_initialization = False
    allows_execution = False
    status_prefix = "🔄 Executing"


class OrchestratorCompleted(OrchestratorState):
    name = "completed"
    has_completed_initialization = True
    skips_initialization = True
    allows_execution = True
    status_prefix = "✅ Complete"


class OrchestratorInitFailed(OrchestratorState):
    name = "init_failed"
    has_completed_initialization = False
    skips_initialization = False
    allows_execution = False
    status_prefix = "❌ Init Failed"


class OrchestratorCompileFailed(OrchestratorState):
    name = "compile_failed"
    has_completed_initialization = True
    skips_initialization = False
    allows_execution = False
    status_prefix = "❌ Compile Failed"


class OrchestratorExecFailed(OrchestratorState):
    name = "exec_failed"
    has_completed_initialization = True
    skips_initialization = False
    allows_execution = False
    status_prefix = "❌ Exec Failed"


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

