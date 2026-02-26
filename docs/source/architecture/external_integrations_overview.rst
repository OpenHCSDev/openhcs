External Integrations Overview
===============================

The Problem: Isolated Processing Pipelines
-------------------------------------------

Scientific image processing rarely happens in isolation. Researchers need to integrate OpenHCS pipelines with external tools: OMERO servers for data storage, Napari/Fiji for visualization, custom analysis tools, and cloud services. Without a unified integration approach, each external tool requires custom code, leading to duplicated logic, inconsistent error handling, and brittle connections that break when tools update.

Executive Summary
-----------------

OpenHCS implements a comprehensive integration strategy with the bioimage analysis ecosystem, providing seamless interoperability with visualization tools (Napari, Fiji) and data management platforms (OMERO). These integrations follow consistent architectural patterns based on inter-process communication (IPC) via ZeroMQ, enabling real-time streaming, remote execution, and location-transparent data access.

This document provides a high-level overview of OpenHCS's integration architecture and how the different components work together to create a unified bioimage analysis platform.

Boundary Split
--------------

The integration stack is now explicitly split across repositories:

- ``zmqruntime`` owns transport and execution lifecycle primitives
  (REQ/REP + PUB/SUB channels, polling, typed execution status contracts).
- ``polystore`` owns streaming payload semantics and receiver-side projection
  utilities (component-mode grouping, batch/debounce engines, viewer payload
  constants).
- ``pyqt-reactive`` owns generic manager/browser UI infrastructure
  (polling shells, tree sync/rebuild, aggregation policies).
- ``openhcs`` owns domain wiring only
  (pipeline/orchestrator semantics, OpenHCS-specific adapters, UX policies).

OpenHCS architecture docs focus on OpenHCS wrapper behavior and link to
external module docs for generic abstraction internals.

Integration Philosophy
----------------------

Core Principles
~~~~~~~~~~~~~~~

1. **Reusable Patterns**: Extract common IPC patterns into generic base classes
2. **Location Transparency**: Same API for local and remote operations
3. **Zero-Copy Performance**: Minimize data movement through shared memory and direct file access
4. **Process Isolation**: Independent processes for stability and resource management
5. **Fail-Loud Design**: Clear error messages, no silent failures
6. **Production-Grade**: Designed for institutional deployment, not just research prototypes

Unified Architecture
~~~~~~~~~~~~~~~~~~~~

All OpenHCS integrations share a common dual-channel ZeroMQ pattern:

.. code-block:: text

   ┌─────────────────────────────────────────────────────────┐
   │                    ZMQ Base Classes                      │
   │  ┌──────────────────────┐  ┌──────────────────────┐    │
   │  │    ZMQServer         │  │    ZMQClient         │    │
   │  │  - Dual channels     │  │  - Connection mgmt   │    │
   │  │  - Ping/pong         │  │  - Auto-spawn        │    │
   │  │  - Process lifecycle │  │  - Multi-instance    │    │
   │  └──────────────────────┘  └──────────────────────┘    │
   └─────────────────────────────────────────────────────────┘
                             │
           ┌─────────────────┼─────────────────┐
           │                 │                 │
           ▼                 ▼                 ▼
   ┌──────────────┐  ┌──────────────┐  ┌──────────────┐
   │   Napari     │  │    Fiji      │  │    OMERO     │
   │  Streaming   │  │  Streaming   │  │  Execution   │
   │              │  │              │  │   Server     │
   └──────────────┘  └──────────────┘  └──────────────┘

Integration Components
----------------------

Napari Integration
~~~~~~~~~~~~~~~~~~

**Purpose**: Real-time visualization of processing results

**Architecture**: OpenHCS wrapper over ``zmqruntime`` transport plus
``polystore`` streaming semantics and receiver projection

**Key Features**:

- Zero-copy shared memory transfer
- Component-aware layer organization
- Persistent viewers across pipeline runs
- Multi-instance support (multiple viewers on different ports)
- Network streaming capability (local → remote)

**Use Cases**:

- Pipeline development and debugging
- Quality control during batch processing
- Multi-step workflow validation
- Remote HPC visualization

**Documentation**: See :doc:`napari_integration_architecture`

OMERO Integration
~~~~~~~~~~~~~~~~~

**Purpose**: Data management and institutional deployment

**Architecture**: Storage backend + execution server + web UI

**Key Features**:

- Zero-copy server-side file access
- Virtual backend pattern (no real filesystem)
- Code-based pipeline serialization
- Web-based pipeline submission
- Automatic instance management

**Use Cases**:

- Institutional core facilities
- High-throughput screening
- Collaborative research
- Teaching and training

**Documentation**: See :doc:`omero_backend_system`

Fiji Integration
~~~~~~~~~~~~~~~~

**Purpose**: Interoperability with ImageJ/Fiji ecosystem

**Architecture**: OpenHCS wrapper over ``zmqruntime`` transport plus
``polystore`` streaming semantics and receiver projection

**Key Features**:

- Zero-copy shared memory transfer
- Automatic hyperstack building from component metadata
- PyImageJ integration for native Fiji functionality
- Persistent viewers across pipeline runs
- Multi-instance support (multiple viewers on different ports)

**Use Cases**:

- Leveraging ImageJ/Fiji plugin ecosystem
- Macro scripting integration
- CZT-based visualization workflows
- Cross-platform bioimage analysis

**Documentation**: See :doc:`fiji_streaming_system`

Architectural Patterns
----------------------

Pattern 1: Dual-Channel ZeroMQ Communication
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Problem**: Need both synchronous request/response and asynchronous data streaming

**Solution**: Separate control and data channels

.. code-block:: text

   Control Channel (REQ/REP):
   - Port: Base port (e.g., 5555, 7777)
   - Purpose: Handshake, commands, status queries
   - Pattern: Synchronous request/response
   
   Data Channel (PUB/SUB):
   - Port: Base port + 1000 (e.g., 6555, 8777)
   - Purpose: Image streaming, progress updates
   - Pattern: Asynchronous publish/subscribe

**Benefits**:

- Control messages don't block data streaming
- Reliable handshake before data transfer
- Independent scaling of control and data throughput

**Implementations**:

- Napari: Image streaming + viewer control
- Fiji: Image streaming + macro execution
- OMERO: Pipeline execution + progress updates

Pattern 2: Instance Management
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Problem**: Need to connect to existing services or start new ones

**Solution**: Check → Connect → Start pattern

.. code-block:: python

   class ServiceManager:
       def connect(self, timeout: int) -> bool:
           # 1. Check if already connected
           if self.is_connected():
               return True
           
           # 2. Try to connect to existing instance
           if self.is_service_running():
               return self._connect_to_service()
           
           # 3. Start new instance if needed
           if self._start_service():
               return self._wait_and_connect(timeout)
           
           return False

**Benefits**:

- Reuses existing instances (faster, resource-efficient)
- Automatic startup when needed (user-friendly)
- Graceful degradation with clear errors

**Implementations**:

- ``NapariStreamVisualizer``: Manages Napari viewer processes
- ``OMEROInstanceManager``: Manages OMERO server connections
- ``ZMQExecutionClient``: Manages execution server connections

Pattern 3: Zero-Copy Data Transfer
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Problem**: Large image arrays are expensive to copy between processes

**Solution**: Shared memory for local IPC, direct file access for storage

**Napari/Fiji Streaming**:

.. code-block:: python

   # Create shared memory block
   shm = shared_memory.SharedMemory(create=True, size=data.nbytes)
   shm_array = np.ndarray(data.shape, dtype=data.dtype, buffer=shm.buf)
   shm_array[:] = data[:]
   
   # Send metadata + shared memory name (not data)
   message = {
       'shm_name': shm.name,
       'shape': data.shape,
       'dtype': str(data.dtype)
   }
   
   # Receiver attaches to same memory
   shm = shared_memory.SharedMemory(name=message['shm_name'])
   data = np.ndarray(message['shape'], dtype=message['dtype'], buffer=shm.buf)

**OMERO Server-Side**:

.. code-block:: python

   # Direct file access (no API overhead)
   local_path = omero_data_dir / user_id / fileset_id / filename
   data = tifffile.imread(local_path)  # Zero-copy mmap possible

**Benefits**:

- Minimal memory overhead
- Maximum throughput
- Reduced latency

Pattern 4: Code-Based Serialization
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Problem**: Pickle fails with enums, custom classes, version mismatches

**Solution**: Generate executable Python code

.. code-block:: python

   # Client: Object → Code
   config_code = generate_python_source(Assignment("config", config_obj))
   # Result: "config = GlobalPipelineConfig(num_workers=4, ...)"
   
   # Server: Code → Object
   namespace = {}
   exec(config_code, namespace)
   config_obj = namespace['config']

**Benefits**:

- Human-readable
- Version-independent
- Debuggable
- Network-safe (JSON strings)

**Implementations**:

- OMERO remote execution
- PyQt UI bidirectional conversion
- Future: Pipeline sharing and templates

Integration Workflows
---------------------

Workflow 1: Local Development with Napari
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: text

   Developer Machine:
     OpenHCS Pipeline
         ↓
     FileManager (Memory/Disk backends)
         ↓
     NapariStreamingBackend
         ↓ (shared memory)
     Napari Viewer Process

**Characteristics**:

- Single machine
- Immediate visual feedback
- Interactive parameter tuning
- Rapid iteration

Workflow 2: Remote Execution with OMERO
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: text

   Researcher's Browser:
     OMERO.web UI
         ↓ (HTTP/AJAX)
     Django Plugin
         ↓ (ZeroMQ)
     
   OMERO Server Machine:
     Execution Server
         ↓ (zero-copy file access)
     OMERO Data
         ↓ (GPU processing)
     Results → OMERO

**Characteristics**:

- Multi-tier architecture
- Server-side GPU processing
- No data movement
- Web-based interface

Workflow 3: Hybrid Remote Execution + Visualization
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: text

   OMERO Server:
     Execution Server
         ↓ (processing)
     Results
         ↓ (network streaming)
     
   Researcher's Workstation:
     Napari Viewer
     (real-time visualization)

**Characteristics**:

- Processing near data (server-side)
- Visualization near user (local)
- Network-based streaming
- Best of both worlds

**Implementation Status**: Architecture supports this, requires:

- Network-aware Napari streaming (change ``localhost`` to remote IP)
- Bandwidth-aware compression
- Authentication/encryption

Performance Characteristics
---------------------------

Napari Streaming
~~~~~~~~~~~~~~~~

================= ============= ============================
Metric            Value         Notes
================= ============= ============================
Latency           ~50ms         Timer-based polling
Throughput        10 images/tick Batch processing
Memory Overhead   ~0%           Shared memory (zero-copy)
Startup Time      ~2s           Viewer process spawn
================= ============= ============================

OMERO Server-Side Execution
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

================= ============= ============================
Metric            Value         Notes
================= ============= ============================
File Access       ~0ms overhead Direct file system access
API Access        ~100ms/image  Network + API overhead
Serialization     ~1ms          Code generation
GPU Speedup       10-100x       vs CPU processing
================= ============= ============================

ZeroMQ Communication
~~~~~~~~~~~~~~~~~~~~

================= ============= ============================
Metric            Value         Notes
================= ============= ============================
Handshake         ~10ms         Ping/pong verification
Message Latency   <1ms          Local IPC
Network Latency   ~10-50ms      Depends on network
Throughput        >1GB/s        Shared memory path
================= ============= ============================

See Also
--------

- :doc:`napari_integration_architecture` - Napari integration details
- :doc:`fiji_streaming_system` - Fiji streaming architecture
- :doc:`omero_backend_system` - OMERO backend architecture
- :doc:`../guides/omero_integration` - OMERO integration guide
- :doc:`../guides/viewer_management` - Viewer management guide
- :doc:`../guides/fiji_viewer_management` - Fiji viewer management
