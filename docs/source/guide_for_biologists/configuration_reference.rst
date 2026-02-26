Configuration Reference
=======================

This section provides a reference of the configuration system of OpenHCS.

How the configuration system works
---------------------------------

In OpenHCS, there are multiple levels of configuration that determine how the software behaves. These levels include:

1. **Global Configuration**: the configuration that applies to the entire OpenHCS installation.
2. **Plate Configuration**: each plate can have its own configuration settings that override the global settings.
3. **Step Configuration**: each step within a plate's pipeline can have its own configuration settings.
4. **Materialization / Viewer Configuration**: for each individual step you can materialize its output to disk or stream it to a viewer (Napari/Fiji); this has its own configuration.

Configurations automatically inherit from higher levels and can be overridden at lower levels. For example, you can run your analysis on all wells, but then open only one well in Napari to look at by using the well filter config at the Napari materialization level. Some options also inherit horizontally; those behaviours are explained in the relevant sections. Some levels do not expose all configuration options (for example, materialization has only materialization-relevant options).


Appendix: Relevant Configuration Options
---------------------------------------

There are several configuration groups used across OpenHCS. Below are commonly used groups and the key options biologists will encounter. (Note: each option usually has a GUI tooltip explaining its purpose.)

GlobalPipelineConfig (main app / pipeline defaults)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- ``num_workers``
   
   How many parallel workers to run for processing (higher = more CPU usage, but faster run times).

- ``materialization_results_path``
   
   Directory name where non-image analysis results (CSV/JSON) are written by default.

- ``use_threading``
   
   If true, use threads instead of processes (useful for some environments, don't touch this unless you know what you're doing).

- ``auto_add_output_plate_to_plate_manager`` (abbreviation: ``auto_add_output_plate``)
   
   If true, when a plate run completes successfully, the computed output plate root (from path planning) is automatically added to Plate Manager as a new orchestrator if it is not already present. This allows immediate visualization of processed results without manual plate addition.
   
   **Environment variable**: ``OPENHCS_AUTO_ADD_OUTPUT_PLATE``
   
   **Default**: ``False``

WellFilterConfig
~~~~~~~~~~~~~~~~~

- ``well_filter``
  
  List, pattern, or integer limiting which wells are included (``None`` = all wells).

- ``well_filter_mode``
  
  ``INCLUDE`` or ``EXCLUDE`` behaviour for the ``well_filter`` list.

ZarrConfig
~~~~~~~~~~~

- ``compression_level``
  
  Compression level to use for Zarr storage (higher = smaller files but slower).

VFSConfig (virtual file system)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- ``read_backend``
  
  Backend used to read input files (auto-detected or explicit choice, don't touch this unless you know what you are doing).

- ``intermediate_backend``

  Backend for storing temporary intermediate results, like those streamed to viewers (memory, disk, etc.).

- ``materialization_backend``
  
  Backend used for explicit materialized outputs (e.g., ``ZARR`` vs ``DISK``).

Typical choices for backends are ``ZARR``, ``DISK`` or ``MEMORY``. ``MEMORY`` stores data in system RAM; ``DISK`` writes regular files (e.g., TIFF); ``ZARR`` stores chunked arrays using the Zarr format (more efficient and space friendly for many workflows).

AnalysisConsolidationConfig
---------------------------

- ``enabled``
  
  Run automatic consolidation of step outputs into summary files.

- ``metaxpress_summary``
  
  Produce MetaXpress-compatible summary format.

- ``well_pattern``, ``file_extensions``, ``exclude_patterns``, ``output_filename``
  
  Controls for which files to include/exclude and the consolidated output name.
  

PlateMetadataConfig
~~~~~~~~~~~~~~~~~~~

- ``barcode``, ``plate_name``, ``plate_id``, ``description``, ``acquisition_user``
  
  Optional metadata fields for the plate.

PathPlanningConfig (directory / output naming)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- ``well_filter`` / ``well_filter_mode``
  
  Inherited from ``StepWellFilterConfig`` unless overridden.

- ``output_dir_suffix``
  
  Suffix appended to generated output folders (default ``"_openhcs"``). For example, if your input folder is ``data/plate1``, the output folder will be ``data/plate1_openhcs``.

- ``global_output_folder``
  
  Optional root folder to place all plate workspaces and outputs.

- ``sub_dir``
  
  Subdirectory name used for image outputs inside a workspace.

StepWellFilterConfig and StepMaterializationConfig
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- Step-level versions of well filtering and path planning. They inherit from higher levels unless overridden.

- ``step_materialization_config.sub_dir``
  
  Default folder for step-level materializations (default ``"checkpoints"``).

VisualizerConfig
~~~~~~~~~~~~~~~~~

- ``temp_directory``
  
  Directory for temporary visualization files (if ``None``, system temp is used).

StreamingConfig (abstract)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- ``persistent``
  
  If true, keeps the streaming service open after initial use.

NapariStreamingConfig
~~~~~~~~~~~~~~~~~~~~~

- ``colormap``
  
  Colormap to use for visualization.

- ``variable_size_handling``
  
  How to handle variable-sized images (pad, rescale, etc.).

- ``site``, ``channel``, ``timepoint``, ``well``, ``z_index``, ``step_name``, ``step_index``, ``source_mode``
  
  Options for whether you'd like to group different variables by slice or stack.

- ``napari_port``, ``napari_host``
  
  Network settings for Napari streaming.

FijiStreamingConfig
~~~~~~~~~~~~~~~~~~~

- ``lut``
  
  Colormap to use for visualization.

- ``auto_contrast``
  
  If true, applies auto-contrast to images.

- ``site``, ``channel``, ``timepoint``, ``well``, ``z_index``, ``step_name``, ``step_index``, ``source_mode``
  
  Options for whether you'd like to group different variables by slice or stack.

- ``fiji_port``, ``fiji_host``, ``fiji_executable_path``
  
  Settings for Fiji/ImageJ streaming and the local executable location.

Notes
~~~~~~

The above lists the configuration options most relevant to biologists using OpenHCS. There are many additional developer-level options in the code documentation (see ``openhcs/core/config.py`` for global defaults). If you don't know what an option does, it's usually best to leave it at its default value.
