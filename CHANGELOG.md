# Changelog

All notable changes to OpenHCS will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

#### Auto-Add Output Plate Feature
- **Automatic output plate registration** - New `auto_add_output_plate_to_plate_manager` config option in GlobalPipelineConfig
  - When enabled, successfully completed plate runs automatically add the computed output plate to Plate Manager
  - Allows immediate visualization of processed results without manual plate addition
  - Environment variable: `OPENHCS_AUTO_ADD_OUTPUT_PLATE`
  - Accessible via Config Window under Pipeline Settings

#### Compilation Architecture Improvements
- **Remote compilation via ZMQ server** - Compilation now happens on the ZMQ execution server instead of locally
  - New shared `ZMQClientService` for managing ZMQ client connections between compilation and execution
  - `CompilationService` and `ZMQExecutionService` now share a single client service instance
  - Improved consistency and resource management across compile/run workflows
  - Requires ZMQ server to be running for compilation (same as execution)

#### LLM-Powered Code Generation Improvements
- **LLM Assist in Code Editor** - Added LLM-powered code generation directly into the OpenHCS code editor
  - **Automatic array backend handling** - Generated functions no longer require manual backend conversions (`cp.asnumpy()`, `cle.pull()`)
  - **Context-aware system prompts** - New `get_system_prompt(code_type)` method provides different prompts for pipeline vs function generation
  - **Array format clarification** - Documentation now specifies (C, Y, X) a.k.a. (Z, Y, X) format for 3D arrays
  - **Memory decorator awareness** - LLM understands `@numpy`, `@cupy`, `@pyclesperanto` decorators and their implications
  - New `LLMPipelineService` for communicating with local LLM endpoints (Ollama)
  - New `LLMChatPanel` widget with chat interface for natural language code generation
  - Integrated LLM panel into `QScintillaCodeEditorDialog` with toggle button
  - Context-aware generation for all code types (pipeline, step, config, function, orchestrator)
  - Comprehensive system prompt with OpenHCS API documentation and examples
  - Background thread execution to keep UI responsive during generation
  - Side-by-side editor/chat layout using QSplitter
  - Automatic code insertion at cursor position
  - Clean markdown formatting removal from generated code
  - Added `requests>=2.31.0` dependency for HTTP communication
  - Comprehensive test suite for LLM service and chat panel

## [0.4.0] - 2025-11-05

### Added

#### Sequential Component Processing
- **Complete implementation of pipeline-wide sequential processing** ([#43](https://github.com/trissim/openhcs/pull/43))
  - Process images across multiple component combinations (e.g., all channels × all z-slices)
  - Per-process backend isolation for parallel execution safety
  - Automatic conflict detection and filtering for variable components
  - Memory clearing between combinations to prevent data leakage
  - Comprehensive validation tests and API improvements
  - Moved configuration from per-step to global `PipelineConfig` level
  - Self-describing backend pickling architecture eliminating duck typing

#### GUI Enhancements
- **Multi-directory plate selection** - Select and process multiple plate directories simultaneously in PyQt GUI
- **Git worktree testing documentation** - Comprehensive guide for testing with git worktrees

#### Configuration System
- **Lazy config merging improvements** - Proper None value resolution in nested dataclasses
- **GlobalPipelineConfig vs PipelineConfig field defaults** - Fixed inheritance and default value handling
- **Placeholder resolution fixes** - Multiple improvements to lazy config context propagation
- **List[Enum] placeholder styling** - Visual feedback when values match inherited defaults

### Fixed

#### Critical Bug Fixes
- **ZMQ viewer instance browser** - Fixed lazy config port scanning to properly detect streaming ports from `PipelineConfig`
- **Race condition in LazyDiscoveryDict** - Fixed concurrent plate initialization issues
- **Pipeline step deletion** - Properly handles duplicate step names
- **Registry isolation** - Multiple fixes for proper component registry isolation
- **Sequential processing component mismatch** - Fixed validation and execution bugs
- **Missing image detection** - Improved error handling and reporting

#### Configuration & UI Fixes
- **Reset parameter not updating placeholders** - Fixed nested form placeholder refresh
- **List[Enum] checkbox race conditions** - Fixed save/load issues and glitchy behavior
- **Component button syncing** - Fixed live form value propagation and group_by changes
- **Lazy resolution for live form values** - Use simple temp object instead of dataclass replace
- **Checkbox group placeholder comparison** - Use enum names instead of values
- **Enabled field styling** - React to context changes like placeholders do

#### Backend & Processing Fixes
- **OMERO backend reconstruction** - Fixed pickling and worker process issues
- **Backend inheritance hierarchy** - Eliminated problematic multiple inheritance
- **Nested dataclass config merging** - Resolve None values before converting to base
- **Enum cache** - Include SequentialComponents in cache
- **Sequential processing memory clearing** - Only clear files from current combination

#### Code Quality & Architecture
- **Eliminated duck typing** - Refactored to use ABCs and explicit interfaces throughout
- **Hardcoded config field accesses** - Replaced with generic merged config pattern everywhere
- **Module-level executable code** - Wrapped in `__main__` guards
- **Code export** - Handle enum lists properly

### Changed

#### Architecture Improvements
- **Backend pickling** - Self-describing architecture with explicit `PicklableBackend` ABC
- **Configuration hierarchy** - Proper GlobalPipelineConfig → PipelineConfig → StepConfig inheritance
- **Registry system** - Improved isolation and caching (9.7x startup improvement)
- **Enum generation caching** - 2800x speedup for colormap generation

#### Refactoring
- **Processing config consolidation** - Unified into single `ProcessingConfig` dataclass
- **Sequential component validation** - Filter conflicts instead of raising errors
- **Compiler config resolution** - Use merged config for global well_filter_config

### Documentation
- Added comprehensive development style review and extraction recommendations
- Updated code review documentation to reflect ABC usage instead of Protocol
- Improved API compatibility documentation after processing_config refactor

---

## [0.3.15] - 2024-10-XX

### Fixed
- Windows unicode escape issue in napari and fiji detached process spawning
- Improved test assertions based on code review feedback
- Applied black formatting and fixed ruff linting issues

---

## Previous Versions

See git history for changes in versions 0.3.14 and earlier.

[0.4.0]: https://github.com/trissim/openhcs/compare/v0.3.15...v0.4.0
[0.3.15]: https://github.com/trissim/openhcs/releases/tag/v0.3.15

