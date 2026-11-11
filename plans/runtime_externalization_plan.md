# Runtime Externalization Plan

Extract a **complete distributed execution framework** from `openhcs/runtime/`
into a standalone `zmqruntime` package. Maximize generic abstractions.

## Coding Conventions

**CRITICAL: Import Style**
- All imports in zmqruntime MUST use explicit full paths, NOT relative imports
- ✅ `from zmqruntime.config import TransportMode`
- ❌ `from .config import TransportMode`
- All imports MUST be at the top of the file, grouped by: stdlib → third-party → zmqruntime
- Use `from __future__ import annotations` for forward references

## Philosophy

The current code mixes **generic patterns** with **openhcs-specific implementations**.
We can extract MORE than just transport utilities by creating ABCs for the patterns.

**Generic patterns to extract:**
- Message protocol (already generic)
- Transport layer (needs constants extraction)
- Queue-based execution server pattern
- Submit/poll/wait client pattern
- Streaming visualizer pattern

**NOT extracted (too coupled):**
- ROI converters (imports `openhcs.core.roi` shapes - would require extracting ROI system too)

**OpenHCS provides only:**
- Concrete implementations that wire up orchestrator, config, FileManager
- ROI conversion using openhcs.core.roi types

## Current Import Analysis

### Files with NO openhcs imports (extractable as-is):
| File | Imports |
|------|---------|
| `zmq_messages.py` | logging, enum, dataclasses only |
| `queue_tracker.py` | logging, threading, time, typing only |

### Files with MINIMAL openhcs imports (extractable with abstraction):
| File | OpenHCS Imports | Abstraction Needed |
|------|-----------------|-------------------|
| `zmq_base.py` | `TransportMode`, constants, `AutoRegisterMeta` | Move TransportMode to zmqruntime, constants as config |
| `zmq_execution_server.py` | `ZMQServer`, messages, `TransportMode`, constants | Use extracted base classes |
| `zmq_execution_client.py` | `ZMQClient`, `TransportMode`, constants | Use extracted base classes |

### Files with HEAVY openhcs imports (stay in openhcs, inherit from ABCs):
| File | OpenHCS Imports |
|------|-----------------|
| `napari_stream_visualizer.py` | FileManager, config, streaming constants |
| `fiji_viewer_server.py` | ZMQServer, streaming constants |
| `fiji_stream_visualizer.py` | FileManager, config |
| `roi_converters.py` | `openhcs.core.roi.*`, `openhcs.constants.streaming` |

## Tiered Analysis

### TIER 1: Core Transport (extractable with minor changes)

| File | Action | Notes |
|------|--------|-------|
| `zmq_messages.py` | Copy verbatim | No changes needed |
| `queue_tracker.py` | Copy verbatim | No changes needed |
| `zmq_base.py` | Extract + abstract | Move TransportMode enum here, parameterize constants |

**Constants to parameterize in zmqruntime:**
```python
# zmqruntime/config.py
@dataclass
class ZMQConfig:
    control_port_offset: int = 1000
    default_port: int = 7777
    ipc_socket_dir: str = "ipc"
    ipc_socket_prefix: str = "zmq"
    ipc_socket_extension: str = ".sock"
    shared_ack_port: int = 7555
```

### TIER 2: Execution Pattern (generic with ABC extraction)

| File | Generic Pattern | OpenHCS-Specific Part |
|------|-----------------|----------------------|
| `zmq_execution_server.py` | Queue-based execution, worker thread, status tracking, progress streaming | `_execute_pipeline()` calls orchestrator |
| `zmq_execution_client.py` | Progress listener, submit/poll/wait flow | `serialize_task()` uses pickle_to_python |

**Abstraction:**
```python
class ExecutionServer(ZMQServer, ABC):
    """Queue-based execution server with progress streaming."""

    @abstractmethod
    def execute_task(self, execution_id: str, request: ExecuteRequest) -> Any:
        """Execute a task. Implementation provides actual execution logic."""
        pass

class ExecutionClient(ZMQClient, ABC):
    """Execution client with progress streaming."""

    @abstractmethod
    def serialize_task(self, task: Any, config: Any) -> dict:
        """Serialize task for transmission. Implementation provides serialization."""
        pass
```

### TIER 3: Streaming Pattern (generic with ABC extraction)

| File | Generic Pattern | OpenHCS-Specific Part |
|------|-----------------|----------------------|
| `napari_stream_visualizer.py` | ZMQ image receiver, process management, ack sending | FileManager, NapariStreamingConfig |
| `fiji_viewer_server.py` | ZMQ image receiver, ImageJ display | openhcs streaming constants |
| `fiji_stream_visualizer.py` | Process launch/stop, health check | openhcs config for paths |

**Abstraction:**
```python
class StreamingVisualizerServer(ZMQServer, ABC):
    """Streaming server that receives and displays images."""

    @abstractmethod
    def display_image(self, image_data: np.ndarray, metadata: dict) -> None:
        """Display received image. Implementation provides display logic."""
        pass

class VisualizerProcessManager(ABC):
    """Manages visualizer subprocess lifecycle."""

    @abstractmethod
    def get_launch_command(self) -> List[str]:
        """Get command to launch visualizer. Implementation provides command."""
        pass
```

### TIER 4: ROI Converters (NOT EXTRACTED - too coupled)

**Decision: Keep roi_converters.py in openhcs**

The ROI converters import:
- `openhcs.constants.streaming.NapariShapeType`
- `openhcs.core.roi.PolygonShape, PolylineShape, EllipseShape, PointShape`

Extracting these would require also extracting the entire ROI type system, which is tightly coupled to openhcs domain concepts. Not worth the complexity.

### Truly OpenHCS-Specific (stays in openhcs)

| File | Why |
|------|-----|
| `execution_server.py` (legacy) | Deprecated, heavy openhcs deps |
| `zmq_execution_server_launcher.py` | CLI entry point for openhcs |
| `omero_instance_manager.py` | OMERO-specific docker management |
| `remote_orchestrator.py` | Deprecated wrapper |
| `roi_converters.py` | Imports openhcs.core.roi types |

## Target Package: `zmqruntime`

Complete distributed execution framework. No domain-specific claims.

### Package Structure

```
external/zmqruntime/
├── pyproject.toml
├── src/
│   └── zmqruntime/
│       ├── __init__.py
│       ├── config.py              # TransportMode enum, ZMQConfig dataclass
│       ├── messages.py            # Message protocol (copy of zmq_messages.py)
│       ├── transport.py           # URL generation, IPC handling
│       ├── server.py              # ZMQServer ABC
│       ├── client.py              # ZMQClient ABC
│       ├── queue_tracker.py       # QueueTracker (copy of queue_tracker.py)
│       ├── ack_listener.py        # Global ack listener pattern
│       │
│       ├── execution/             # TIER 2: Execution pattern
│       │   ├── __init__.py
│       │   ├── server.py          # ExecutionServer ABC (queue-based)
│       │   └── client.py          # ExecutionClient ABC (submit/poll/wait)
│       │
│       └── streaming/             # TIER 3: Streaming pattern
│           ├── __init__.py
│           ├── server.py          # StreamingVisualizerServer ABC
│           └── process_manager.py # VisualizerProcessManager ABC
└── tests/
    ├── test_messages.py
    ├── test_transport.py
    ├── test_queue_tracker.py
    └── test_execution.py
```

**Note:** Shapes/ROI converters are NOT extracted (see Tier 4 decision above).

### Dependencies

```toml
[project]
name = "zmqruntime"
version = "0.1.0"
description = "Generic ZMQ-based distributed execution framework"
dependencies = [
    "pyzmq>=22.0",
]

[project.optional-dependencies]
registry = ["metaclass-registry"]   # For AutoRegisterMeta (optional)
dev = ["pytest", "pytest-cov"]
```

### Public API

```python
# Core (Tier 1)
from zmqruntime import (
    TransportMode, ZMQConfig,
    ControlMessageType, ResponseType, ExecutionStatus, MessageFields,
    ZMQServer, ZMQClient,
    QueueTracker, GlobalQueueTrackerRegistry,
    get_zmq_transport_url, get_ipc_socket_path,
)

# Execution (Tier 2)
from zmqruntime.execution import ExecutionServer, ExecutionClient

# Streaming (Tier 3)
from zmqruntime.streaming import StreamingVisualizerServer, VisualizerProcessManager
```

## Implementation Plan

### Phase 1: Create package skeleton

**Files to create:**
```bash
mkdir -p external/zmqruntime/src/zmqruntime/execution
mkdir -p external/zmqruntime/src/zmqruntime/streaming
mkdir -p external/zmqruntime/tests
touch external/zmqruntime/src/zmqruntime/__init__.py
touch external/zmqruntime/src/zmqruntime/execution/__init__.py
touch external/zmqruntime/src/zmqruntime/streaming/__init__.py
```

**pyproject.toml content:**
```toml
[build-system]
requires = ["hatchling"]
build-backend = "hatchling.build"

[project]
name = "zmqruntime"
version = "0.1.0"
description = "Generic ZMQ-based distributed execution framework"
readme = "README.md"
requires-python = ">=3.10"
dependencies = [
    "pyzmq>=22.0",
]

[project.optional-dependencies]
registry = ["metaclass-registry"]
dev = ["pytest", "pytest-cov"]

[tool.hatch.build.targets.wheel]
packages = ["src/zmqruntime"]
```

### Phase 2: Extract Tier 1 (Core Transport)

#### Step 2.1: config.py
Create `zmqruntime/config.py`:
```python
# zmqruntime/config.py
"""Configuration types for ZMQ transport."""
from __future__ import annotations

from dataclasses import dataclass
from enum import Enum


class TransportMode(Enum):
    """Transport mode for ZMQ communication."""
    TCP = "tcp"
    IPC = "ipc"


@dataclass
class ZMQConfig:
    """Configuration for ZMQ transport."""
    control_port_offset: int = 1000
    default_port: int = 7777
    ipc_socket_dir: str = "ipc"
    ipc_socket_prefix: str = "zmq"
    ipc_socket_extension: str = ".sock"
    shared_ack_port: int = 7555
    app_name: str = "zmqruntime"  # Used for ~/.{app_name}/ipc/
```

#### Step 2.2: messages.py
Copy `openhcs/runtime/zmq_messages.py` verbatim to `zmqruntime/messages.py`.
No changes needed - file has no openhcs imports.

#### Step 2.3: queue_tracker.py
Copy `openhcs/runtime/queue_tracker.py` verbatim to `zmqruntime/queue_tracker.py`.
No changes needed - file has no openhcs imports.

#### Step 2.4: transport.py
Extract URL generation functions from `openhcs/runtime/zmq_base.py`:
```python
# zmqruntime/transport.py
"""Transport utilities for ZMQ communication."""
from __future__ import annotations

import platform
from pathlib import Path
from typing import Optional

from zmqruntime.config import TransportMode, ZMQConfig

_default_config = ZMQConfig()

def get_default_transport_mode() -> TransportMode:
    """Get platform-appropriate transport mode."""
    return TransportMode.TCP if platform.system() == 'Windows' else TransportMode.IPC

def get_ipc_socket_path(port: int, config: ZMQConfig = None) -> Optional[Path]:
    """Get IPC socket path for a given port (Unix/Mac only)."""
    config = config or _default_config
    if platform.system() == 'Windows':
        return None
    ipc_dir = Path.home() / f".{config.app_name}" / config.ipc_socket_dir
    socket_name = f"{config.ipc_socket_prefix}-{port}{config.ipc_socket_extension}"
    return ipc_dir / socket_name

def get_zmq_transport_url(port: int, host: str = 'localhost',
                          mode: TransportMode = None, config: ZMQConfig = None) -> str:
    """Get ZMQ transport URL for given port/host/mode."""
    config = config or _default_config
    mode = mode or get_default_transport_mode()
    if mode == TransportMode.IPC:
        socket_path = get_ipc_socket_path(port, config)
        return f"ipc://{socket_path}"
    else:
        return f"tcp://{host}:{port}"

def remove_ipc_socket(port: int, config: ZMQConfig = None) -> bool:
    """Remove stale IPC socket file."""
    socket_path = get_ipc_socket_path(port, config)
    if socket_path and socket_path.exists():
        socket_path.unlink()
        return True
    return False
```

#### Step 2.5: server.py
Extract `ZMQServer` ABC from `openhcs/runtime/zmq_base.py`:
- Remove `from openhcs.runtime.zmq_messages import ...` → `from .messages import ...`
- Remove `from openhcs.constants.constants import ...` → use `ZMQConfig`
- Remove `from openhcs.core.config.pipeline_config import TransportMode` → `from .config import TransportMode`
- Make `AutoRegisterMeta` optional via try/except import

#### Step 2.6: client.py
Extract `ZMQClient` ABC from `openhcs/runtime/zmq_base.py`:
- Same import changes as server.py

#### Step 2.7: ack_listener.py
Extract global ack listener pattern:
```python
# zmqruntime/ack_listener.py
"""Global acknowledgment listener for ZMQ visualizers."""
from __future__ import annotations

import threading
from typing import Callable, Optional

import zmq

class GlobalAckListener:
    """Singleton listener for acknowledgment messages from visualizers."""
    _instance: Optional['GlobalAckListener'] = None
    _lock = threading.Lock()

    def __new__(cls):
        with cls._lock:
            if cls._instance is None:
                cls._instance = super().__new__(cls)
                cls._instance._initialized = False
            return cls._instance

    def __init__(self):
        if self._initialized:
            return
        self._callbacks: list[Callable] = []
        self._running = False
        self._thread: Optional[threading.Thread] = None
        self._initialized = True

    def register_callback(self, callback: Callable) -> None:
        """Register callback for ack messages."""
        self._callbacks.append(callback)

    def start(self, port: int) -> None:
        """Start listening on given port."""
        # Implementation: create PULL socket, start thread
        pass

    def stop(self) -> None:
        """Stop the listener."""
        pass
```

### Phase 3: Extract Tier 2 (Execution Pattern)

#### Step 3.1: execution/server.py
Extract `ExecutionServer` ABC from `openhcs/runtime/zmq_execution_server.py`:

**What to extract (generic):**
- Queue worker thread management (`_start_queue_worker`, `_queue_worker_loop`)
- Active executions tracking (`self.active_executions`)
- Progress queue management (`self.progress_queue`)
- Status info generation (`get_status_info`, `_create_pong_response`)
- Message handling dispatch (`handle_control_message`)

**What stays abstract:**
```python
@abstractmethod
def execute_task(self, execution_id: str, request: ExecuteRequest) -> Any:
    """Execute a task. Subclass provides actual execution logic."""
    pass
```

#### Step 3.2: execution/client.py
Extract `ExecutionClient` ABC from `openhcs/runtime/zmq_execution_client.py`:

**What to extract (generic):**
- Progress listener thread (`_start_progress_listener`, `_progress_listener_loop`)
- Submit/poll/wait pattern (`submit_execution`, `poll_status`, `wait_for_completion`)
- Connection management

**What stays abstract:**
```python
@abstractmethod
def serialize_task(self, task: Any, config: Any) -> dict:
    """Serialize task for transmission. Subclass provides serialization logic."""
    pass
```

### Phase 4: Extract Tier 3 (Streaming Pattern)

#### Step 4.1: streaming/server.py
Extract `StreamingVisualizerServer` ABC:

**What to extract (generic):**
- ZMQ image receiver pattern
- Ack sending logic
- Message deserialization

**What stays abstract:**
```python
@abstractmethod
def display_image(self, image_data: np.ndarray, metadata: dict) -> None:
    """Display received image. Subclass provides display logic."""
    pass
```

#### Step 4.2: streaming/process_manager.py
Extract `VisualizerProcessManager` ABC:

**What to extract (generic):**
- Subprocess launch/stop
- Health checking
- Port management

**What stays abstract:**
```python
@abstractmethod
def get_launch_command(self) -> List[str]:
    """Get command to launch visualizer. Subclass provides command."""
    pass

@abstractmethod
def get_launch_env(self) -> dict:
    """Get environment variables for subprocess."""
    pass
```

### Phase 5: Update openhcs (NO Tier 4 - shapes stay in openhcs)

#### Step 5.1: Add zmqruntime dependency
Add to `openhcs/pyproject.toml`:
```toml
dependencies = [
    ...
    "zmqruntime",
]
```

#### Step 5.2: Update openhcs/runtime/zmq_base.py
Change imports:
```python
# Before
from openhcs.runtime.zmq_messages import ...
from openhcs.constants.constants import ...
from openhcs.core.config.pipeline_config import TransportMode

# After
from zmqruntime import (
    TransportMode, ZMQConfig, ZMQServer, ZMQClient,
    ControlMessageType, ResponseType, MessageFields, ...
)
```

#### Step 5.3: Create concrete implementations
```python
# openhcs/runtime/zmq_execution_server.py
from zmqruntime.execution import ExecutionServer
from zmqruntime import ExecuteRequest

class OpenHCSExecutionServer(ExecutionServer):
    """OpenHCS-specific execution server."""

    def execute_task(self, execution_id: str, request: ExecuteRequest) -> Any:
        """Execute pipeline using orchestrator."""
        # Existing _execute_pipeline logic stays here
        return self._execute_pipeline(execution_id, request)
```

#### Step 5.4: Update import sites
Run:
```bash
rg "from openhcs.runtime.zmq_messages import" openhcs/
rg "from openhcs.runtime.zmq_base import" openhcs/
```
Update each site to import from zmqruntime.

### Phase 6: Verification

#### Step 6.1: Verify no openhcs imports in zmqruntime
```bash
rg "from openhcs" external/zmqruntime/
rg "import openhcs" external/zmqruntime/
# Should return nothing
```

#### Step 6.2: Run zmqruntime tests
```bash
cd external/zmqruntime
pytest tests/ -v
```

#### Step 6.3: Run openhcs tests
```bash
cd /path/to/openhcs
pytest tests/test_main.py -v  # Main integration test
pytest tests/ -k zmq -v       # All ZMQ-related tests
```

### Phase 7: Clean up

1. Delete duplicated code from openhcs/runtime/ that's now in zmqruntime
2. Keep only concrete implementations that inherit from zmqruntime ABCs
3. Update documentation

## What Stays in openhcs/runtime/

After extraction, these concrete implementations remain:

| File | What It Does |
|------|--------------|
| `zmq_execution_server.py` | `OpenHCSExecutionServer(ExecutionServer)` - implements `execute_task()` with orchestrator |
| `zmq_execution_client.py` | `OpenHCSExecutionClient(ExecutionClient)` - implements `serialize_task()` with pickle_to_python |
| `zmq_execution_server_launcher.py` | CLI entry point for openhcs (unchanged) |
| `napari_stream_visualizer.py` | `OpenHCSNapariVisualizer(StreamingVisualizerServer)` - implements `display_image()` with napari |
| `fiji_viewer_server.py` | `OpenHCSFijiViewer(StreamingVisualizerServer)` - implements `display_image()` with ImageJ |
| `fiji_stream_visualizer.py` | `OpenHCSFijiProcessManager(VisualizerProcessManager)` - implements `get_launch_command()` |
| `roi_converters.py` | ROI conversion (unchanged - uses openhcs.core.roi types) |
| `omero_instance_manager.py` | OMERO docker management (unchanged) |
| `execution_server.py` | Legacy deprecated (unchanged) |
| `remote_orchestrator.py` | Legacy deprecated (unchanged) |

## OpenHCS Import Sites to Update

Files that currently import from `openhcs.runtime.zmq_*`:
```bash
# Find all import sites
rg "from openhcs.runtime.zmq" openhcs/ --files-with-matches
```

Expected sites:
```
openhcs/runtime/zmq_execution_server.py      # Uses ZMQServer
openhcs/runtime/zmq_execution_client.py      # Uses ZMQClient
openhcs/runtime/zmq_execution_server_launcher.py  # Uses server
openhcs/runtime/napari_stream_visualizer.py  # Uses ZMQServer
openhcs/runtime/fiji_viewer_server.py        # Uses ZMQServer
openhcs/io/streaming.py                      # Uses messages/constants
openhcs/io/napari_stream.py                  # Uses streaming
openhcs/io/fiji_stream.py                    # Uses streaming
openhcs/pyqt_gui/widgets/shared/zmq_server_manager.py  # Uses server registry
openhcs/pyqt_gui/widgets/shared/services/zmq_execution_service.py  # Uses client
```

## Validation Checklist

### Unit tests for zmqruntime (new tests to write):
- [ ] `test_config.py`: TransportMode enum, ZMQConfig defaults
- [ ] `test_messages.py`: Message serialization/deserialization roundtrip
- [ ] `test_transport.py`: URL generation (TCP/IPC), socket path generation
- [ ] `test_queue_tracker.py`: Queue tracking, registry singleton
- [ ] `test_execution_server.py`: Queue worker (mock execute_task), status tracking
- [ ] `test_execution_client.py`: Progress listener (mock callback), submit/poll flow

### Integration tests (existing openhcs tests should pass):
- [ ] `test_main.py` - Main integration test
- [ ] Any tests in `tests/` that use ZMQ execution

### Import verification:
```bash
# zmqruntime has no openhcs imports
rg "from openhcs" external/zmqruntime/
rg "import openhcs" external/zmqruntime/
# Should return nothing

# All openhcs runtime files import from zmqruntime
rg "from zmqruntime" openhcs/runtime/
# Should show imports in all files that use base classes
```

## Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Package name | `zmqruntime` | Generic, no domain claims |
| Scope | 3 tiers (transport, execution, streaming) | ROI too coupled to extract |
| AutoRegisterMeta | Optional dep on metaclass-registry | Avoid hard dependency |
| UI callback | Registration pattern in GlobalAckListener | No GUI coupling |
| Shapes/ROI | NOT extracted | Too coupled to openhcs.core.roi |
| Execution pattern | ABC with abstract execute_task | openhcs provides orchestrator logic |
| Streaming pattern | ABC with abstract display_image | openhcs provides viewer logic |
| Config | ZMQConfig dataclass | Parameterizes all constants |

## Benefits

1. **zmqruntime is a complete framework** - transport, execution, streaming patterns
2. **openhcs/runtime/ shrinks dramatically** - only concrete wiring remains
3. **Other projects can use zmqruntime** - for any ZMQ-based distributed execution
4. **Clear separation** - generic patterns vs domain logic
5. **Testable in isolation** - zmqruntime tests don't need openhcs

## Risk Mitigation

| Risk | Mitigation |
|------|------------|
| Breaking existing functionality | Run full test suite after each phase |
| Missing imports | Use `rg` to find all import sites before changing |
| Circular dependencies | zmqruntime has no openhcs deps by design |
| Performance regression | Measure startup time before/after |

## Estimated Effort

| Phase | Effort | Notes |
|-------|--------|-------|
| Phase 1: Skeleton | 30 min | Create dirs, pyproject.toml |
| Phase 2: Core Transport | 2-3 hours | Most complex - extract and adapt imports |
| Phase 3: Execution | 1-2 hours | Extract ABCs, keep logic |
| Phase 4: Streaming | 1-2 hours | Extract ABCs, keep logic |
| Phase 5: Update openhcs | 2-3 hours | Update all import sites |
| Phase 6: Verification | 1 hour | Run tests, fix issues |
| Phase 7: Cleanup | 30 min | Remove dead code |

**Total: ~8-12 hours**
