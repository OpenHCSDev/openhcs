Pattern Grouping and Special Output Path Resolution
====================================================

Overview
--------

This document explains the fundamental principles of how OpenHCS handles pattern grouping, special output path resolution, and the interaction between ``group_by``, ``variable_components``, and the special I/O system. Understanding these principles is essential for debugging path collisions and understanding compilation behavior.

**Critical Insight**: The ``group_by`` parameter serves dual purposes:
1. For **dict patterns**: Specifies what dimension the dictionary keys represent
2. For **list patterns**: Controls pattern grouping and special output namespacing

This dual purpose is intentional and enables compile-time path planning with deterministic, semantic paths.

First Principles
----------------

Pattern Types and Internal Representation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

OpenHCS internally normalizes all function patterns to a dictionary format for uniform processing:

**Dict Patterns** (explicit):

.. code-block:: python

   # User writes:
   FunctionStep(
       func={'1': analyze_nuclei, '2': analyze_gfp},
       group_by=GroupBy.CHANNEL
   )
   
   # Internal representation: (unchanged)
   {'1': analyze_nuclei, '2': analyze_gfp}

**List Patterns** (normalized to dict):

.. code-block:: python

   # User writes:
   FunctionStep(func=[normalize, tophat])
   
   # Internal representation:
   {'default': [normalize, tophat]}

**Single Patterns** (normalized to dict):

.. code-block:: python

   # User writes:
   FunctionStep(func=(normalize, {}))
   
   # Internal representation:
   {'default': (normalize, {})}

**The "default" Key Convention**:
- String ``"default"`` is used as the internal dict key for non-dict patterns
- Converted to ``None`` when used as a special output group key
- See ``openhcs/formats/func_arg_prep.py::iter_pattern_items()`` and ``openhcs/core/pipeline/path_planner.py::extract_attributes()``

The Role of ``group_by``
~~~~~~~~~~~~~~~~~~~~~~~~~

**For Dict Patterns**: Semantic Meaning of Keys
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The ``group_by`` parameter tells OpenHCS what dimension the dictionary keys represent:

.. code-block:: python

   # Keys are channel numbers
   FunctionStep(
       func={'1': analyze_nuclei, '2': analyze_gfp},
       group_by=GroupBy.CHANNEL  # Keys '1' and '2' are channel numbers
   )
   
   # Keys are well identifiers
   FunctionStep(
       func={'control': process_control, 'treatment': process_treatment},
       group_by=GroupBy.WELL  # Keys are well names
   )

**For List Patterns**: Pattern Grouping and Output Namespacing
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

For list patterns, ``group_by`` controls how patterns are organized during discovery and how special outputs are namespaced:

.. code-block:: python

   # WITHOUT group_by: All patterns processed together
   FunctionStep(
       func=(normalize, {}),
       group_by=None,  # or GroupBy.NONE
       variable_components=[VariableComponents.SITE, VariableComponents.CHANNEL]
   )
   # Pattern discovery returns:
   # {"default": ["A01_s{iii}_w1_z001.tif", "A01_s{iii}_w2_z001.tif"]}
   # Special outputs: All patterns write to SAME path → COLLISION!
   
   # WITH group_by: Patterns grouped by component
   FunctionStep(
       func=(normalize, {}),
       group_by=GroupBy.CHANNEL,
       variable_components=[VariableComponents.SITE, VariableComponents.CHANNEL]
   )
   # Pattern discovery returns:
   # {"1": ["A01_s{iii}_w1_z001.tif"], "2": ["A01_s{iii}_w2_z001.tif"]}
   # Special outputs: Each channel gets its own path → NO COLLISION!

The Dual Purpose of ``group_by``
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Why does ``group_by`` affect list patterns?**

The system uses ``group_by`` for list patterns to enable:

1. **Semantic Grouping**: Patterns are organized by meaningful component values (channel 1, channel 2) rather than arbitrary indices
2. **Deterministic Paths**: Special output paths are known at compile time, not runtime
3. **Cross-Step Communication**: Later steps can reference special outputs by component (e.g., "get cell_counts for channel 1")
4. **Compile-Time Validation**: Path collisions are detected during compilation, not execution

**Alternative Considered**: Runtime collision detection with auto-generated suffixes

.. code-block:: python

   # Runtime collision detection (NOT IMPLEMENTED):
   if vfs_path in already_saved_paths:
       vfs_path = f"{vfs_path.stem}_pattern{index}{vfs_path.suffix}"
   
   # Problems:
   # 1. Non-deterministic paths (unknown until runtime)
   # 2. Cross-step communication breaks (can't reference by name)
   # 3. Loss of semantic meaning (cell_counts_pattern0.pkl vs cell_counts_w1.pkl)

**Conclusion**: Using ``group_by`` for list patterns provides compile-time guarantees and semantic clarity.

Pattern Discovery and Grouping Flow
------------------------------------

Understanding the complete flow from pattern discovery to execution is essential for debugging path issues.

Step 1: Pattern Discovery
~~~~~~~~~~~~~~~~~~~~~~~~~~

The ``PatternDiscoveryEngine`` discovers patterns based on ``variable_components``:

.. code-block:: python

   # Configuration:
   variable_components = [VariableComponents.SITE, VariableComponents.CHANNEL]
   group_by = GroupBy.CHANNEL

   # Files in directory:
   # A01_s001_w1_z001_t001.tif
   # A01_s001_w2_z001_t001.tif
   # A01_s002_w1_z001_t001.tif
   # A01_s002_w2_z001_t001.tif

   # Step 1: Generate patterns (based on variable_components)
   patterns = [
       "A01_s{iii}_w1_z001_t001.tif",  # Site varies, channel=1 fixed
       "A01_s{iii}_w2_z001_t001.tif"   # Site varies, channel=2 fixed
   ]

   # Step 2: Group patterns (based on group_by)
   if group_by == GroupBy.CHANNEL:
       # Parse each pattern to extract channel value
       # "A01_s{iii}_w1_z001_t001.tif" → replace {iii} with 001 → parse → channel='1'
       grouped_patterns = {
           "1": ["A01_s{iii}_w1_z001_t001.tif"],
           "2": ["A01_s{iii}_w2_z001_t001.tif"]
       }
   else:
       # No grouping
       grouped_patterns = ["A01_s{iii}_w1_z001_t001.tif", "A01_s{iii}_w2_z001_t001.tif"]

**Key Files**:
- ``openhcs/formats/pattern/pattern_discovery.py::auto_detect_patterns()`` (line 233-277)
- ``openhcs/formats/pattern/pattern_discovery.py::group_patterns_by_component()`` (line 157-202)

Step 2: Path Planning (Compilation)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The ``PathPlanner`` determines execution groups and creates special output paths:

.. code-block:: python

   # For list patterns with group_by:
   def _get_execution_groups(step, step_index):
       # Resolve group_by via ObjectState (handles lazy dataclasses)
       group_by = step_state.get_saved_resolved_value("processing_config.group_by")

       if group_by and group_by != GroupBy.NONE:
           # Get component keys from orchestrator
           return ["1", "2"]  # For CHANNEL with 2 channels
       else:
           return [None]  # No grouping

   # Create special output paths for each group:
   execution_groups = ["1", "2"]
   for output_key in special_outputs:
       paths_by_group = {
           "1": "A01_w1_cell_counts_step7.pkl",
           "2": "A01_w2_cell_counts_step7.pkl"
       }

**Critical**: The path planner must use ``ObjectState.get_saved_resolved_value()`` to resolve ``group_by`` from lazy dataclasses, NOT direct ``getattr()`` access.

**Key Files**:
- ``openhcs/core/pipeline/path_planner.py::_get_execution_groups()`` (line 105-146)
- ``openhcs/core/pipeline/path_planner.py::_build_paths_by_group()`` (line 145-157)
- ``openhcs/core/pipeline/compiler.py::initialize_step_plans_for_context()`` (line 495-505)

Step 3: Pattern Preparation (Execution)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The ``prepare_patterns_and_functions()`` normalizes patterns to dict format:

.. code-block:: python

   # Input from pattern discovery:
   patterns = {"1": ["w1_pattern"], "2": ["w2_pattern"]}  # Already grouped
   func = (normalize, {})  # List pattern

   # Normalization:
   grouped_patterns = patterns  # Already a dict, use as-is
   component_to_funcs = {
       "1": [(normalize, {})],  # Same function for channel 1
       "2": [(normalize, {})]   # Same function for channel 2
   }

**Key Files**:
- ``openhcs/formats/func_arg_prep.py::prepare_patterns_and_functions()`` (line 96-273)

Step 4: Execution Loop
~~~~~~~~~~~~~~~~~~~~~~

The execution loop processes each component group separately:

.. code-block:: python

   # For each component value:
   for comp_val, pattern_list in grouped_patterns.items():
       # comp_val = "1" or "2"
       exec_func = component_to_funcs[comp_val]

       # For each pattern in this component group:
       for pattern in pattern_list:
           _process_single_pattern_group(
               ...,
               component_value=comp_val,  # "1" or "2"
               ...
           )

           # Inside _process_single_pattern_group:
           component_key = str(component_value)  # "1" or "2"

           # Select special outputs for this component:
           special_outputs_for_component = _select_special_plan_for_component(
               special_outputs_by_group,  # {"1": {...}, "2": {...}}
               component_key,  # "1" or "2"
               default_plan
           )
           # Returns: {"cell_counts": {"path": "A01_w1_cell_counts_step7.pkl"}}

**Key Files**:
- ``openhcs/core/steps/function_step.py::process()`` (line 1316-1356)
- ``openhcs/core/steps/function_step.py::_process_single_pattern_group()`` (line 701-900)
- ``openhcs/core/steps/function_step.py::_select_special_plan_for_component()`` (line 78-90)

Common Issues and Debugging
----------------------------

Issue 1: Special Output Path Collision with List Patterns
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Symptom**:

.. code-block:: text

   FileExistsError: Path already exists: /path/to/results/A01_cell_counts_step7.pkl

**Root Cause**: Multiple patterns trying to write to the same special output path.

**Diagnosis**:

1. Check if ``group_by`` is being resolved correctly during path planning:

   .. code-block:: python

      # Add debug logging in path_planner.py::_get_execution_groups()
      logger.info(f"🔍 PATH_PLANNER: group_by={group_by} (via ObjectState)")
      logger.info(f"🔍 PATH_PLANNER: Resolved groups: {result}")

2. Check if ``special_outputs_by_group`` has the expected groups:

   .. code-block:: python

      # Add debug logging in function_step.py::_process_single_pattern_group()
      logger.info(f"🔍 AVAILABLE_GROUPS: {list(special_outputs_by_group.keys())}")
      logger.info(f"🔍 COMPONENT_KEY: {component_key}")

**Common Causes**:

1. **``group_by`` is ``None`` during path planning**: The path planner is reading ``group_by`` before it's been resolved from lazy dataclass

   **Fix**: Ensure ``step_state_map`` is passed to ``PathPlanner`` and use ``ObjectState.get_saved_resolved_value()``

2. **Pattern discovery not grouping patterns**: ``auto_detect_patterns()`` not receiving ``group_by`` parameter

   **Fix**: Ensure ``group_by`` is passed from ``FunctionStep.process()`` to ``microscope_handler.auto_detect_patterns()``

3. **Orchestrator not initialized**: Cannot resolve component keys for ``group_by``

   **Fix**: Ensure orchestrator is initialized before compilation

Issue 2: ``group_by`` Resolves to ``None`` During Compilation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Symptom**: Path planner logs show ``group_by=None`` even though step configuration has ``group_by=GroupBy.CHANNEL``

**Root Cause**: Lazy dataclass not resolved via ObjectState during path planning.

**Diagnosis**:

.. code-block:: python

   # Check if using direct getattr (WRONG):
   group_by = getattr(step.processing_config, "group_by", None)  # Returns unresolved lazy value

   # Should use ObjectState (CORRECT):
   group_by = step_state.get_saved_resolved_value("processing_config.group_by")

**Fix**: Update ``PathPlanner._get_execution_groups()`` to accept ``step_index`` and use ``step_state_map`` for resolution.

**Key Commit**: The compiler was refactored to resolve step attributes via ObjectState instead of getattr with fallback.

Issue 3: Understanding "default" vs ``None`` in Group Keys
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Confusion**: Why do some logs show ``"default"`` and others show ``None``?

**Explanation**:

- **Internal dict keys**: Use string ``"default"`` for non-dict patterns (see ``func_arg_prep.py::iter_pattern_items()``)
- **Special output group keys**: Convert ``"default"`` to ``None`` (see ``path_planner.py::extract_attributes()`` line 59)

.. code-block:: python

   # Internal representation:
   grouped_patterns = {"default": [pattern1, pattern2]}

   # Special output groups:
   special_outputs_by_group = {None: {"cell_counts": {"path": "..."}}}

   # Conversion happens here:
   normalized_key = None if group_key == "default" else group_key

**When you see**:
- ``dict_key_for_funcplan = "default"``: List/single pattern execution
- ``special_outputs_by_group = {None: ...}``: Ungrouped special outputs
- ``component_key = None``: No component grouping

Variable Components vs Group By
--------------------------------

Understanding the Difference
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**``variable_components``**: Controls which components vary during pattern discovery

.. code-block:: python

   variable_components = [VariableComponents.SITE, VariableComponents.CHANNEL]
   # Discovers patterns where site and channel vary:
   # "A01_s{iii}_w1_z001.tif"  ← site varies, channel=1 fixed
   # "A01_s{iii}_w2_z001.tif"  ← site varies, channel=2 fixed

**``group_by``**: Controls how discovered patterns are organized and how special outputs are namespaced

.. code-block:: python

   group_by = GroupBy.CHANNEL
   # Groups patterns by channel value:
   # {"1": ["A01_s{iii}_w1_z001.tif"], "2": ["A01_s{iii}_w2_z001.tif"]}
   # Creates channel-specific special output paths

**Key Distinction**:
- ``variable_components``: "What varies in the pattern?" (pattern discovery)
- ``group_by``: "How should we organize the patterns?" (grouping and namespacing)

Example Combinations
~~~~~~~~~~~~~~~~~~~~~

**Example 1: Site varies, no grouping**

.. code-block:: python

   FunctionStep(
       func=(normalize, {}),
       variable_components=[VariableComponents.SITE],
       group_by=None
   )
   # Discovers: ["A01_s{iii}_w1_z001.tif"]
   # Groups: {"default": ["A01_s{iii}_w1_z001.tif"]}
   # Special outputs: All sites write to same path

**Example 2: Site and channel vary, group by channel**

.. code-block:: python

   FunctionStep(
       func=(normalize, {}),
       variable_components=[VariableComponents.SITE, VariableComponents.CHANNEL],
       group_by=GroupBy.CHANNEL
   )
   # Discovers: ["A01_s{iii}_w1_z001.tif", "A01_s{iii}_w2_z001.tif"]
   # Groups: {"1": ["A01_s{iii}_w1_z001.tif"], "2": ["A01_s{iii}_w2_z001.tif"]}
   # Special outputs: Each channel gets its own path

**Example 3: Dict pattern (group_by specifies key meaning)**

.. code-block:: python

   FunctionStep(
       func={'1': analyze_nuclei, '2': analyze_gfp},
       variable_components=[VariableComponents.SITE],
       group_by=GroupBy.CHANNEL  # Keys '1' and '2' are channel numbers
   )
   # Discovers: ["A01_s{iii}_w1_z001.tif", "A01_s{iii}_w2_z001.tif"]
   # Groups: {"1": ["A01_s{iii}_w1_z001.tif"], "2": ["A01_s{iii}_w2_z001.tif"]}
   # Routes: channel 1 → analyze_nuclei, channel 2 → analyze_gfp


