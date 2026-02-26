Component System
================

OpenHCS uses a dynamic component system to organize microscopy data processing across different dimensions. The system provides two main enums - AllComponents and VariableComponents - that serve different purposes in the processing pipeline.

Understanding Component Types
-----------------------------

OpenHCS distinguishes between components that are available for user configuration and those used for internal operations:

**AllComponents**: Complete component set including the multiprocessing axis
**VariableComponents**: User-selectable components excluding the multiprocessing axis
**GroupBy**: VariableComponents with an additional NONE option for routing

.. code-block:: python

   from openhcs.constants import AllComponents, VariableComponents, GroupBy

   # AllComponents includes all dimensions
   list(AllComponents)  # [SITE, CHANNEL, Z_INDEX, WELL]

   # VariableComponents excludes multiprocessing axis (WELL by default)
   list(VariableComponents)  # [SITE, CHANNEL, Z_INDEX]

   # GroupBy adds NONE option to VariableComponents
   list(GroupBy)  # [SITE, CHANNEL, Z_INDEX, NONE]

Dynamic Enum Generation
-----------------------

Components are created dynamically from configuration when first accessed:

.. code-block:: python

   # Enums are generated lazily from ComponentConfiguration
   from openhcs.constants import get_openhcs_config
   
   config = get_openhcs_config()
   # Configuration determines:
   # - All available components (SITE, CHANNEL, Z_INDEX, WELL)
   # - Multiprocessing axis (WELL)
   # - Remaining components for user selection (SITE, CHANNEL, Z_INDEX)

The configuration drives which components are available and how they're filtered for different use cases.

When to Use Each Component Type
-------------------------------

AllComponents: Internal Operations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Use AllComponents for operations that need access to the complete dimensional space:

.. code-block:: python

   # Cache addressing requires full component set
   orchestrator.cache_component_keys([AllComponents.WELL, AllComponents.SITE])

   # Getting component keys for any dimension
   axis_values = orchestrator.get_component_keys(MULTIPROCESSING_AXIS)  # Dynamic axis
   sites = orchestrator.get_component_keys(AllComponents.SITE)

**When to use AllComponents**:
- Cache operations and full-space addressing
- Orchestrator component key operations
- Internal system operations that need complete dimensional access

VariableComponents: User Configuration
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Use VariableComponents for step configuration and user-facing operations:

.. code-block:: python

   from openhcs.core.steps.function_step import FunctionStep
   from openhcs.core.pipeline_config import LazyStepMaterializationConfig

   # Step configuration with user-selectable components
   step = FunctionStep(
       func=(normalize_images, {}),
       variable_components=[VariableComponents.SITE, VariableComponents.CHANNEL],
       materialization_config=LazyStepMaterializationConfig()
   )

**When to use VariableComponents**:
- Step configuration in pipelines
- UI component dropdowns and selectors
- User-facing configuration options
- Pattern discovery and grouping operations

GroupBy: Function Routing
~~~~~~~~~~~~~~~~~~~~~~~~~

Use GroupBy for dictionary function patterns and conditional routing:

.. code-block:: python

   # Route different channels to different functions
   step = FunctionStep(
       func={
           '1': (analyze_nuclei, {}),     # Channel 1 → nuclei analysis
           '2': (analyze_neurites, {})    # Channel 2 → neurite analysis
       },
       group_by=GroupBy.CHANNEL,
       variable_components=[VariableComponents.SITE]
   )

   # No grouping option
   step = FunctionStep(
       func=(process_all_data, {}),
       group_by=GroupBy.NONE,
       variable_components=[VariableComponents.SITE]
   )

.. seealso::

   :doc:`../architecture/pattern_grouping_and_special_outputs`
      Comprehensive explanation of how ``group_by`` works for both dict and list patterns, including special output namespacing

**GroupBy properties**:

.. code-block:: python

   # Access underlying component value
   assert GroupBy.CHANNEL.component == "channel"
   assert GroupBy.NONE.component is None

   # String value for pattern operations
   component_string = GroupBy.CHANNEL.value  # "channel"

Multiprocessing Axis
--------------------

The multiprocessing axis determines how parallel processing is partitioned:

.. code-block:: python

   from openhcs.constants import MULTIPROCESSING_AXIS

   # Get multiprocessing axis component (WELL by default)
   axis = MULTIPROCESSING_AXIS  # Returns the configured multiprocessing component

   # Use in orchestrator operations
   wells_to_process = orchestrator.get_component_keys(MULTIPROCESSING_AXIS)

**Key characteristics**:
- Excluded from VariableComponents (not user-selectable)
- Included in AllComponents (available for internal operations)
- Used by compiler and orchestrator for task partitioning
- Configurable through ComponentConfiguration

Practical Usage Examples
------------------------

Step Configuration
~~~~~~~~~~~~~~~~~~

.. code-block:: python

   from openhcs.core.steps.function_step import FunctionStep
   from openhcs.processing.backends.processors.numpy_processor import create_composite

   # Process each site separately, combining channels
   composite_step = FunctionStep(
       func=create_composite,
       variable_components=[VariableComponents.SITE],
       name="create_composite"
   )

Cache Operations
~~~~~~~~~~~~~~~~

.. code-block:: python

   # Cache all component types for fast access
   orchestrator.cache_component_keys(list(AllComponents))

   # Get cached component keys for current multiprocessing axis
   from openhcs.constants import MULTIPROCESSING_AXIS
   available_axis_values = orchestrator.get_component_keys(MULTIPROCESSING_AXIS)

Pattern Discovery
~~~~~~~~~~~~~~~~~

.. code-block:: python

   # Group patterns by component for organization
   if group_by and group_by != GroupBy.NONE:
       component_string = group_by.value
       grouped_patterns = pattern_discovery.group_patterns_by_component(
           patterns, component=component_string
       )

UI Component Population
~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   # Populate dropdown with user-selectable components
   component_options = list(VariableComponents)
   
   # Populate GroupBy selector with NONE option
   groupby_options = list(GroupBy)

Integration with Configuration
-----------------------------

The component system integrates with OpenHCS configuration for customization:

.. code-block:: python

   from openhcs.core.components.framework import ComponentConfigurationFactory

   # Custom component configuration
   config = ComponentConfigurationFactory.create_configuration(
       component_enum=MyCustomEnum,
       multiprocessing_axis=MyCustomEnum.BATCH,
       default_variable=[MyCustomEnum.SAMPLE],
       default_group_by=MyCustomEnum.CONDITION
   )

This enables different microscopy setups to define their own component dimensions while maintaining the same processing patterns.

Performance Characteristics
---------------------------

- **Lazy Loading**: Enums created only when first accessed
- **Caching**: Enum instances cached to avoid recreation  
- **Memory Overhead**: Minimal - single enum instances per component set
- **Access Time**: O(1) after initial creation

The lazy loading ensures minimal startup overhead while caching provides fast subsequent access.
