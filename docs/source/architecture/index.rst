======================
Architecture Reference
======================

Technical documentation of OpenHCS's architecture for developers who need to understand internal implementation details.

**Prerequisites**: :doc:`../concepts/index` | **Integration**: :doc:`../guides/index`

Core System Architecture
========================

Fundamental systems that define OpenHCS architecture.

.. toctree::
   :maxdepth: 1

   plugin_registry_system
   plugin_registry_advanced
   function_pattern_system
   function_registry_system
   function_reference_pattern
   custom_function_registration_system
   pipeline_compilation_system
   special_io_system
   pattern_grouping_and_special_outputs
   roi_system
   analysis_consolidation_system
   experimental_analysis_system
   dict_pattern_case_study

Configuration Systems
=====================

Lazy configuration, dual-axis resolution, inheritance detection, and field path systems.

.. toctree::
   :maxdepth: 1

   configuration_framework
   dynamic_dataclass_factory
   context_system
   orchestrator_configuration_management
   component_configuration_framework

Storage and Memory
==================

File management, memory types, and backend systems.

.. toctree::
   :maxdepth: 1

   storage_and_memory_system
   memory_type_system
   napari_streaming_system
   omero_backend_system

External Integrations
=====================

Integration with external tools and platforms (Napari, OMERO, Fiji).

.. toctree::
   :maxdepth: 1

   external_integrations_overview
   streaming_boundary_and_wrappers
   napari_integration_architecture
   omero_backend_system
   fiji_streaming_system

System Integration
==================

How OpenHCS components work together and integrate with external systems.

.. toctree::
   :maxdepth: 1

   system_integration
   microscope_handler_integration
   ezstitcher_to_openhcs_evolution

Component Systems
================

Component validation, integration, and processing.

.. toctree::
   :maxdepth: 1

   component_validation_system
   component_system_integration
   component_processor_metaprogramming

Advanced Processing
==================

GPU management, multiprocessing, and performance optimization.

.. toctree::
   :maxdepth: 1

   multiprocessing_coordination_system
   gpu_resource_management
   compilation_system_detailed
   concurrency_model
   orchestrator_cleanup_guarantees

Metaprogramming and Parsing
===========================

Dynamic code generation and parser systems.

.. toctree::
   :maxdepth: 1

   parser_metaprogramming_system
   pattern_detection_system

User Interface Systems
=====================

TUI architecture, UI development patterns, and form management systems.

.. toctree::
   :maxdepth: 1

   tui_system
   widget_protocol_system
   abstract_manager_widget
   abstract_table_browser
   list_item_preview_system
   flash_animation_system
   scope_visual_feedback_system
   plate_manager_services
   batch_workflow_service
   progress_runtime_projection_system
   zmq_server_browser_system
   parameter_form_lifecycle
   parameter_form_service_architecture
   ui_services_architecture
   field_change_dispatcher
   parametric_widget_creation
   code_ui_interconversion
   service-layer-architecture
   gui_performance_patterns
   cross_window_update_optimization
   scope_window_factory_system
   service_registry_integration

Development Tools
=================

Practical tools for OpenHCS development workflows.

.. toctree::
   :maxdepth: 1

   step-editor-generalization

Quick Start Paths
==================

**New to OpenHCS?** Start with :doc:`function_pattern_system` → :doc:`configuration_framework` → :doc:`storage_and_memory_system`

**Configuration Systems?** Focus on :doc:`dynamic_dataclass_factory` → :doc:`context_system` → :doc:`orchestrator_configuration_management`

**Real-Time Visualization?** Begin with :doc:`napari_integration_architecture` → :doc:`napari_streaming_system` → :doc:`roi_system` → :doc:`storage_and_memory_system`

**OMERO Integration?** Start with :doc:`omero_backend_system` → :doc:`storage_and_memory_system`

**External Integrations?** Start with :doc:`external_integrations_overview` → :doc:`napari_integration_architecture` → :doc:`fiji_streaming_system` → :doc:`omero_backend_system`

**UI Development?** Start with :doc:`widget_protocol_system` → :doc:`abstract_manager_widget` → :doc:`parametric_widget_creation` → :doc:`field_change_dispatcher` → :doc:`ui_services_architecture` → :doc:`batch_workflow_service` → :doc:`zmq_server_browser_system` → :doc:`tui_system`

**System Integration?** Jump to :doc:`system_integration` → :doc:`special_io_system` → :doc:`microscope_handler_integration`

**Performance Optimization?** Focus on :doc:`gpu_resource_management` → :doc:`compilation_system_detailed` → :doc:`multiprocessing_coordination_system`

**Architecture Quick Start**: A short, curated orientation is available at :doc:`quick_start` — three recommended reading paths (Core systems, Integrations, UI) to get developers productive quickly.

.. toctree::
   :maxdepth: 1

   quick_start
