# plan_01_llm_pipeline_generator.md

## Component: LLM-Powered Code Generation for OpenHCS Code Editor

### Objective

Add LLM-powered code generation directly into the OpenHCS code editor (QScintillaCodeEditorDialog). This provides LLM assistance for ALL code editing contexts automatically: pipelines, steps, configs, functions, and orchestrator code. Users can describe what they want in natural language, and the LLM generates appropriate code that gets inserted into the editor.

### Plan

This feature adds an "LLM Assist" button to the existing code editor dialog. When clicked, it opens a side panel with a chat interface. The user describes what they want, the LLM generates code based on the current editing context (pipeline/step/config/etc.), and the generated code is inserted into the editor. This reuses 100% of the existing code editor infrastructure and automatically works for all code editing contexts.

#### 1. Create LLM Service Module

**File**: `openhcs/pyqt_gui/services/llm_pipeline_service.py`

**Purpose**: Handle all LLM communication and prompt construction.

**Implementation Details**:

```python
"""
LLM Pipeline Generation Service

Handles communication with LLM endpoints to generate OpenHCS pipeline code
from natural language descriptions.
"""

import logging
import requests
from typing import Optional, Dict, Any
from pathlib import Path

logger = logging.getLogger(__name__)


class LLMPipelineService:
    """
    Service for generating OpenHCS pipelines using LLM.
    
    Sends user requests to LLM endpoint with comprehensive system prompt
    containing OpenHCS API documentation and examples.
    """
    
    def __init__(self, api_endpoint: str = "http://localhost:11434/api/generate",
                 model: str = "qwen2.5-coder:32b"):
        """
        Initialize LLM service.
        
        Args:
            api_endpoint: LLM API endpoint URL (default: Ollama local endpoint)
            model: Model name to use for generation
        """
        self.api_endpoint = api_endpoint
        self.model = model
        self.system_prompt = self._build_system_prompt()
    
    def _build_system_prompt(self) -> str:
        """
        Build comprehensive system prompt with OpenHCS documentation.
        
        Returns:
            Complete system prompt string
        """
        # Read example pipeline from basic_pipeline.py
        basic_pipeline_path = Path(__file__).parent.parent.parent.parent / "tests" / "basic_pipeline.py"
        try:
            with open(basic_pipeline_path, 'r') as f:
                example_pipeline = f.read()
        except Exception as e:
            logger.warning(f"Could not load example pipeline: {e}")
            example_pipeline = "# Example pipeline not available"
        
        prompt = f"""You are an expert OpenHCS pipeline generator. Generate complete, runnable OpenHCS pipeline code based on user descriptions.

# OpenHCS Architecture Principles

1. **Stateless Functions**: All processing functions must be pure input/output with no side effects
2. **Enum-Driven Patterns**: Use enums for configuration, not magic strings
3. **Fail-Loud Behavior**: No defensive programming, no hasattr checks, no silent error handling
4. **Dataclass Patterns**: Use dataclasses for structured configuration
5. **No Duck Typing**: Explicit interfaces and ABCs only

# OpenHCS Pipeline API

## Core Imports

```python
from openhcs.core.steps.function_step import FunctionStep
from openhcs.core.config.pipeline_config import (
    LazyProcessingConfig, LazyStepWellFilterConfig, LazyStepMaterializationConfig,
    LazyNapariStreamingConfig, LazyFijiStreamingConfig
)
from openhcs.constants.constants import VariableComponents, InputSource, GroupBy
```

## FunctionStep Structure

FunctionStep is the core building block. It accepts:

- `func`: Single function, tuple (func, kwargs), list of functions, or dict for channel/well-specific routing
- `name`: Human-readable step name
- `processing_config`: LazyProcessingConfig for variable_components, group_by, input_source
- `step_well_filter_config`: LazyStepWellFilterConfig for well filtering
- `step_materialization_config`: LazyStepMaterializationConfig for saving outputs
- `napari_streaming_config`: LazyNapariStreamingConfig for Napari visualization
- `fiji_streaming_config`: LazyFijiStreamingConfig for Fiji/ImageJ visualization

## Function Pattern Examples

### Single Function
```python
FunctionStep(func=normalize_images, name="normalize")
```

### Function with Parameters
```python
FunctionStep(
    func=(stack_percentile_normalize, {{
        'low_percentile': 1.0,
        'high_percentile': 99.0
    }}),
    name="normalize"
)
```

### Function Chain (Sequential)
```python
FunctionStep(
    func=[
        (gaussian_blur, {{'sigma': 2.0}}),
        threshold_otsu,
        binary_opening
    ],
    name="segment"
)
```

### Channel-Specific Routing (Dictionary)
```python
FunctionStep(
    func={{
        "DAPI": [(gaussian_blur, {{'sigma': 1.0}}), threshold_otsu],
        "GFP": [(enhance_contrast, {{}}), detect_cells],
        "RFP": [normalize_illumination, segment]
    }},
    group_by=GroupBy.CHANNEL,
    name="channel_processing"
)
```

## Available Processing Functions

### NumPy/CPU Functions
```python
from openhcs.processing.backends.processors.numpy_processor import (
    stack_percentile_normalize,
    create_projection,
    create_composite
)
```

### CuPy/GPU Functions
```python
from openhcs.processing.backends.processors.cupy_processor import (
    stack_percentile_normalize,  # GPU version
    tophat,
    gaussian_filter
)
```

### PyTorch/GPU Functions
```python
from openhcs.processing.backends.processors.torch_processor import (
    stack_percentile_normalize,  # PyTorch version
    gaussian_filter_torch
)
```

### Analysis Functions
```python
from openhcs.processing.backends.analysis.cell_counting_cpu import count_cells_single_channel
from openhcs.processing.backends.stitching.ashlar_cpu import ashlar_compute_tile_positions_cpu, assemble_stack_cpu
```

### pyclesperanto (GPU OpenCL)
```python
from openhcs.pyclesperanto import gaussian_blur, threshold_otsu, binary_opening
```

## Configuration Options

### VariableComponents
Controls which dimensions vary during processing:
- `VariableComponents.SITE`: Process each site/field separately
- `VariableComponents.CHANNEL`: Process each channel separately
- `VariableComponents.Z_INDEX`: Process each Z-slice separately
- `VariableComponents.TIMEPOINT`: Process each timepoint separately
- `VariableComponents.WELL`: Process each well separately

### InputSource
- `InputSource.PREVIOUS_STEP`: Read from previous step output (default)
- `InputSource.PIPELINE_START`: Read from original input (for position computation, QC)

### GroupBy
- `GroupBy.CHANNEL`: Route functions by channel
- `GroupBy.WELL`: Route functions by well
- `GroupBy.ANALYSIS_TYPE`: Route by analysis type

## Example Pipeline

{example_pipeline}

# Your Task

Generate complete OpenHCS pipeline code based on user descriptions. Always:

1. Start with proper imports
2. Create empty `pipeline_steps = []` list
3. Define each step with FunctionStep
4. Append each step to pipeline_steps
5. Use appropriate variable_components for the task
6. Include helpful step names
7. Add comments explaining each step

Output ONLY the Python code, no explanations."""

        return prompt
    
    def generate_code(self, user_request: str, code_type: str = 'pipeline') -> str:
        """
        Generate code from user request based on context.

        Args:
            user_request: Natural language description of desired code
            code_type: Type of code to generate ('pipeline', 'step', 'config', 'function', 'orchestrator')

        Returns:
            Generated Python code as string

        Raises:
            Exception: If LLM request fails
        """
        try:
            # Build context-specific prompt suffix
            context_suffix = {
                'pipeline': "Generate complete pipeline_steps list with FunctionStep objects.",
                'step': "Generate a single FunctionStep object.",
                'config': "Generate a configuration object (LazyProcessingConfig, LazyStepWellFilterConfig, etc.).",
                'function': "Generate a function pattern (single function, list, or dict).",
                'orchestrator': "Generate complete orchestrator code with plate_paths, pipeline_data, and configs."
            }.get(code_type, "Generate OpenHCS code.")

            # Construct request payload (Ollama format)
            payload = {
                "model": self.model,
                "prompt": f"{self.system_prompt}\n\nContext: {context_suffix}\n\nUser Request:\n{user_request}\n\nGenerated Code:",
                "stream": False,
                "options": {
                    "temperature": 0.2,  # Low temperature for more deterministic code generation
                    "top_p": 0.9,
                }
            }

            logger.info(f"Sending request to LLM: {self.api_endpoint} (code_type={code_type})")
            response = requests.post(self.api_endpoint, json=payload, timeout=60)
            response.raise_for_status()

            result = response.json()
            generated_code = result.get('response', '')

            # Clean up code (remove markdown code blocks if present)
            generated_code = self._clean_generated_code(generated_code)

            logger.info(f"Successfully generated {code_type} code")
            return generated_code

        except requests.exceptions.RequestException as e:
            logger.error(f"LLM request failed: {e}")
            raise Exception(f"Failed to connect to LLM service: {e}")
        except Exception as e:
            logger.error(f"Code generation failed: {e}")
            raise
    
    def _clean_generated_code(self, code: str) -> str:
        """
        Clean generated code by removing markdown formatting.
        
        Args:
            code: Raw generated code
            
        Returns:
            Cleaned Python code
        """
        # Remove markdown code blocks
        if code.startswith("```python"):
            code = code[len("```python"):].lstrip()
        if code.startswith("```"):
            code = code[3:].lstrip()
        if code.endswith("```"):
            code = code[:-3].rstrip()
        
        return code.strip()
```

**Key Points**:
- Uses requests library for HTTP communication (already in dependencies via scripts/requirements.txt)
- Default endpoint is Ollama local API (http://localhost:11434/api/generate)
- System prompt includes complete OpenHCS API documentation
- Reads example pipeline from `tests/basic_pipeline.py` for reference
- Low temperature (0.2) for deterministic code generation
- Cleans markdown formatting from generated code

#### 2. Create Chat Panel Widget

**File**: `openhcs/pyqt_gui/widgets/llm_chat_panel.py`

**Purpose**: Reusable chat panel widget that can be embedded in the code editor.

**Implementation Details**:

```python
"""
LLM Chat Panel Widget

Embeddable chat panel for LLM-powered code generation.
Can be integrated into any code editor or dialog.
"""

import logging
from typing import Optional, Callable

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QTextEdit, QPushButton,
    QLabel, QMessageBox
)
from PyQt6.QtCore import Qt, QThread, pyqtSignal
from PyQt6.QtGui import QFont

from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator
from openhcs.pyqt_gui.services.llm_pipeline_service import LLMPipelineService

logger = logging.getLogger(__name__)


class LLMGenerationThread(QThread):
    """Background thread for LLM generation to keep UI responsive."""

    finished = pyqtSignal(str)  # Emits generated code
    error = pyqtSignal(str)     # Emits error message

    def __init__(self, service: LLMPipelineService, user_request: str, code_type: str):
        super().__init__()
        self.service = service
        self.user_request = user_request
        self.code_type = code_type

    def run(self):
        """Execute LLM generation in background."""
        try:
            generated_code = self.service.generate_code(self.user_request, self.code_type)
            self.finished.emit(generated_code)
        except Exception as e:
            self.error.emit(str(e))


class LLMChatPanel(QWidget):
    """
    Chat panel for LLM-powered code generation.

    Designed to be embedded in code editor as a side panel.
    Emits signal when code is generated for parent to handle insertion.
    """

    # Signal emitted when code is generated
    code_generated = pyqtSignal(str)

    def __init__(self, parent=None, color_scheme: Optional[PyQt6ColorScheme] = None,
                 code_type: str = None):
        """
        Initialize chat panel.

        Args:
            parent: Parent widget
            color_scheme: Color scheme for consistent styling
            code_type: Type of code being edited ('pipeline', 'step', 'config', etc.)
        """
        super().__init__(parent)

        self.color_scheme = color_scheme or PyQt6ColorScheme()
        self.style_generator = StyleSheetGenerator(self.color_scheme)
        self.code_type = code_type
        self.llm_service = LLMPipelineService()
        self.generation_thread: Optional[LLMGenerationThread] = None

        self.setup_ui()
        self.setup_connections()

    def setup_ui(self):
        """Setup UI components."""
        layout = QVBoxLayout(self)
        layout.setContentsMargins(5, 5, 5, 5)
        layout.setSpacing(5)

        # Title label
        context_name = {
            'pipeline': 'Pipeline',
            'step': 'Step',
            'config': 'Config',
            'function': 'Function',
            'orchestrator': 'Orchestrator'
        }.get(self.code_type, 'Code')

        title = QLabel(f"LLM Assist - {context_name}")
        title.setFont(QFont("Arial", 9, QFont.Weight.Bold))
        title.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text)};")
        layout.addWidget(title)

        # Chat history display (read-only, compact)
        self.chat_history = QTextEdit()
        self.chat_history.setReadOnly(True)
        self.chat_history.setStyleSheet(f"""
            QTextEdit {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.input_bg)};
                color: {self.color_scheme.to_hex(self.color_scheme.text)};
                border: 1px solid {self.color_scheme.to_hex(self.color_scheme.border)};
                border-radius: 3px;
                padding: 4px;
                font-family: 'Courier New', monospace;
                font-size: 9pt;
            }}
        """)
        layout.addWidget(self.chat_history, stretch=2)

        # User input area (compact)
        input_label = QLabel("Describe what you want:")
        input_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text)}; font-size: 9pt;")
        layout.addWidget(input_label)

        self.user_input = QTextEdit()
        self.user_input.setPlaceholderText("Example: Add a step that normalizes images using percentile normalization")
        self.user_input.setStyleSheet(f"""
            QTextEdit {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.input_bg)};
                color: {self.color_scheme.to_hex(self.color_scheme.text)};
                border: 1px solid {self.color_scheme.to_hex(self.color_scheme.border)};
                border-radius: 3px;
                padding: 4px;
                font-size: 9pt;
            }}
        """)
        self.user_input.setMaximumHeight(80)
        layout.addWidget(self.user_input, stretch=1)

        # Button row (compact)
        button_layout = QHBoxLayout()
        button_layout.setSpacing(4)

        self.generate_button = QPushButton("Generate")
        self.generate_button.setStyleSheet(self.style_generator.generate_button_style())
        self.generate_button.setMinimumHeight(28)
        button_layout.addWidget(self.generate_button)

        self.clear_button = QPushButton("Clear")
        self.clear_button.setStyleSheet(self.style_generator.generate_button_style())
        self.clear_button.setMinimumHeight(28)
        button_layout.addWidget(self.clear_button)

        layout.addLayout(button_layout)

        # Apply panel background
        self.setStyleSheet(f"""
            QWidget {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.window_bg)};
            }}
        """)

    def setup_connections(self):
        """Setup signal/slot connections."""
        self.generate_button.clicked.connect(self.on_generate_clicked)
        self.clear_button.clicked.connect(self.on_clear_clicked)

    def on_generate_clicked(self):
        """Handle generate button click."""
        user_request = self.user_input.toPlainText().strip()

        if not user_request:
            QMessageBox.warning(self, "Empty Request", "Please describe what you want first.")
            return

        # Disable generate button during generation
        self.generate_button.setEnabled(False)
        self.generate_button.setText("Generating...")

        # Add user request to chat history
        self.append_to_history(f"<b>You:</b> {user_request}")

        # Clear input
        self.user_input.clear()

        # Start background generation
        self.generation_thread = LLMGenerationThread(
            self.llm_service, user_request, self.code_type
        )
        self.generation_thread.finished.connect(self.on_generation_finished)
        self.generation_thread.error.connect(self.on_generation_error)
        self.generation_thread.start()

    def on_generation_finished(self, generated_code: str):
        """Handle successful generation."""
        # Re-enable button
        self.generate_button.setEnabled(True)
        self.generate_button.setText("Generate")

        # Add success message to history
        self.append_to_history(f"<b>LLM:</b> Code generated (inserted into editor)")

        # Emit signal for parent to handle insertion
        self.code_generated.emit(generated_code)

    def on_generation_error(self, error_message: str):
        """Handle generation error."""
        # Re-enable button
        self.generate_button.setEnabled(True)
        self.generate_button.setText("Generate")

        # Show error in chat history
        self.append_to_history(f"<b style='color: red;'>Error:</b> {error_message}")

        # Show error dialog
        QMessageBox.critical(self, "Generation Failed",
                           f"Failed to generate code:\n\n{error_message}")

    def on_clear_clicked(self):
        """Clear chat history."""
        self.chat_history.clear()

    def append_to_history(self, message: str):
        """Append message to chat history."""
        self.chat_history.append(message)
        self.chat_history.append("")  # Add blank line for spacing

        # Scroll to bottom
        scrollbar = self.chat_history.verticalScrollBar()
        scrollbar.setValue(scrollbar.maximum())
```

**Key Points**:
- Inherits from QWidget (embeddable panel, not standalone dialog)
- Compact design suitable for side panel in code editor
- Emits `code_generated` signal instead of using callback
- Context-aware: shows code type in title ("LLM Assist - Pipeline")
- Uses QThread for background generation
- Consistent styling with PyQt6ColorScheme
- Smaller fonts and tighter spacing for panel layout

#### 3. Integrate LLM Panel into Code Editor

**File**: `openhcs/pyqt_gui/services/simple_code_editor.py`

**Changes Required**:

**Location 1**: Add imports at top of file (after line 20)

```python
from PyQt6.QtWidgets import QSplitter
from openhcs.pyqt_gui.widgets.llm_chat_panel import LLMChatPanel
```

**Location 2**: Modify `QScintillaCodeEditorDialog.__init__()` (around line 153)

Add instance variable after line 178:
```python
self.llm_panel: Optional[LLMChatPanel] = None
self.llm_panel_visible = False
```

**Location 3**: Modify `_setup_ui()` method (around line 199)

Replace the editor widget addition (currently line 219: `main_layout.addWidget(self.editor)`) with a splitter:

```python
# Create splitter for editor and LLM panel
self.splitter = QSplitter(Qt.Orientation.Horizontal)
self.splitter.setChildrenCollapsible(False)

# Add editor to splitter
self.splitter.addWidget(self.editor)

# Create LLM panel (initially hidden)
self.llm_panel = LLMChatPanel(
    parent=self,
    color_scheme=self.color_scheme,
    code_type=self.code_type
)
self.llm_panel.code_generated.connect(self._on_llm_code_generated)
self.llm_panel.setVisible(False)
self.splitter.addWidget(self.llm_panel)

# Set initial splitter sizes (editor takes all space when LLM panel hidden)
self.splitter.setSizes([700, 300])

main_layout.addWidget(self.splitter)
```

**Location 4**: Modify button layout in `_setup_ui()` (around line 222)

Add LLM Assist button before Save button:

```python
# Buttons
button_layout = QHBoxLayout()

# LLM Assist button (toggle)
self.llm_assist_btn = QPushButton("LLM Assist")
self.llm_assist_btn.setCheckable(True)
self.llm_assist_btn.setChecked(False)
self.llm_assist_btn.clicked.connect(self._toggle_llm_panel)
button_layout.addWidget(self.llm_assist_btn)

self.save_btn = QPushButton("Save")
# Support Shift+Click for 'Save without close'
self.save_btn.clicked.connect(self._on_save_clicked)
button_layout.addWidget(self.save_btn)

self.cancel_btn = QPushButton("Cancel")
self.cancel_btn.clicked.connect(self.reject)
button_layout.addWidget(self.cancel_btn)

button_layout.addStretch()
main_layout.addLayout(button_layout)
```

**Location 5**: Add new methods after `_handle_save()` method (around line 945)

```python
def _toggle_llm_panel(self, checked: bool):
    """Toggle LLM assist panel visibility."""
    self.llm_panel_visible = checked
    self.llm_panel.setVisible(checked)

    if checked:
        # Show panel - adjust splitter sizes
        self.splitter.setSizes([500, 400])
        self.llm_panel.user_input.setFocus()
    else:
        # Hide panel - editor takes all space
        self.splitter.setSizes([900, 0])
        self.editor.setFocus()

def _on_llm_code_generated(self, generated_code: str):
    """Handle code generated by LLM panel."""
    # Insert generated code at cursor position
    cursor_line, cursor_index = self.editor.getCursorPosition()
    self.editor.insert(generated_code)

    # Optionally: auto-hide panel after insertion
    # self.llm_assist_btn.setChecked(False)
    # self._toggle_llm_panel(False)
```

**Key Points**:
- Uses QSplitter to create side-by-side layout (editor | LLM panel)
- LLM Assist button is checkable (toggle on/off)
- Panel is initially hidden, shows when button clicked
- Generated code is inserted at cursor position in editor
- Works automatically for ALL code types (pipeline, step, config, function, orchestrator)
- No changes needed to any calling code - feature is built into the editor itself
- Reuses 100% of existing code editor infrastructure

#### 4. Update Dependencies (if needed)

**File**: `pyproject.toml` or `requirements.txt`

**Check**: Verify `requests` library is in dependencies.

Looking at `scripts/requirements.txt`, `requests>=2.31.0` is already present. However, this is only for release scripts.

**Action**: Add `requests` to main dependencies in `pyproject.toml` if not already present.

In `pyproject.toml`, find the `dependencies` section and ensure it includes:
```toml
dependencies = [
    # ... existing dependencies ...
    "requests>=2.31.0",
]
```

If `requests` is already in dependencies (check the file), no changes needed.

#### 5. Testing Strategy

**Manual Testing Steps**:

1. **Test LLM Service**:
   - Ensure Ollama is running locally: `ollama serve`
   - Ensure model is available: `ollama pull qwen2.5-coder:32b`
   - Test service directly in Python REPL:
     ```python
     from openhcs.pyqt_gui.services.llm_pipeline_service import LLMPipelineService
     service = LLMPipelineService()
     code = service.generate_code("normalize images and apply gaussian blur", code_type='pipeline')
     print(code)
     ```

2. **Test LLM Panel in Pipeline Editor**:
   - Open pipeline editor in GUI
   - Click "Code" button to open code editor
   - Click "LLM Assist" button in code editor
   - Verify panel slides in from right side
   - Verify panel shows "LLM Assist - Pipeline" title
   - Enter request: "Add a step that normalizes images using percentile normalization"
   - Click "Generate"
   - Verify button shows "Generating..." and is disabled
   - Verify generated code is inserted into editor at cursor position
   - Verify panel shows success message in chat history

3. **Test LLM Panel in Step Editor**:
   - Open step parameter editor
   - Click "View Code" button
   - Click "LLM Assist" button
   - Verify panel shows "LLM Assist - Step" title
   - Generate step code and verify insertion

4. **Test LLM Panel in Config Editor**:
   - Open any config window (GlobalPipelineConfig, etc.)
   - Click "View Code" button
   - Click "LLM Assist" button
   - Verify panel shows "LLM Assist - Config" title
   - Generate config code and verify insertion

5. **Test Error Handling**:
   - Stop Ollama service
   - Try to generate code
   - Verify error message appears in panel chat history and QMessageBox
   - Verify button re-enables after error

6. **Test Panel Toggle**:
   - Click "LLM Assist" button to show panel
   - Click again to hide panel
   - Verify splitter resizes correctly
   - Verify editor gets focus when panel hidden

**Integration Testing**:

Create test file `tests/gui/test_llm_code_generation.py`:

```python
"""Tests for LLM code generation feature."""

import pytest
from unittest.mock import Mock, patch
from PyQt6.QtWidgets import QApplication

from openhcs.pyqt_gui.services.llm_pipeline_service import LLMPipelineService
from openhcs.pyqt_gui.widgets.llm_chat_panel import LLMChatPanel


def test_llm_service_builds_system_prompt():
    """Test that system prompt is built correctly."""
    service = LLMPipelineService()
    assert "OpenHCS Architecture Principles" in service.system_prompt
    assert "FunctionStep" in service.system_prompt
    assert "VariableComponents" in service.system_prompt


@patch('openhcs.pyqt_gui.services.llm_pipeline_service.requests.post')
def test_llm_service_generates_code(mock_post):
    """Test successful code generation."""
    # Mock LLM response
    mock_post.return_value.json.return_value = {
        'response': 'pipeline_steps = []\\n# Generated code'
    }
    mock_post.return_value.raise_for_status = Mock()

    service = LLMPipelineService()
    code = service.generate_code("normalize images", code_type='pipeline')

    assert "pipeline_steps" in code
    assert mock_post.called


@patch('openhcs.pyqt_gui.services.llm_pipeline_service.requests.post')
def test_llm_service_handles_errors(mock_post):
    """Test error handling."""
    mock_post.side_effect = Exception("Connection failed")

    service = LLMPipelineService()
    with pytest.raises(Exception, match="Failed to connect"):
        service.generate_code("test", code_type='pipeline')


def test_llm_service_context_specific_prompts():
    """Test that different code types get appropriate context."""
    service = LLMPipelineService()

    # Test different code types
    for code_type in ['pipeline', 'step', 'config', 'function', 'orchestrator']:
        # Should not raise exception
        # (actual generation would require LLM service running)
        assert code_type in ['pipeline', 'step', 'config', 'function', 'orchestrator']


def test_chat_panel_creation(qtbot):
    """Test chat panel can be created."""
    panel = LLMChatPanel(code_type='pipeline')
    qtbot.addWidget(panel)

    assert panel.code_type == 'pipeline'
    assert panel.llm_service is not None
    assert panel.generate_button is not None
    assert panel.user_input is not None


def test_chat_panel_signal_emission(qtbot):
    """Test that panel emits code_generated signal."""
    panel = LLMChatPanel(code_type='step')
    qtbot.addWidget(panel)

    # Connect signal to mock
    mock_handler = Mock()
    panel.code_generated.connect(mock_handler)

    # Simulate successful generation
    test_code = "step = FunctionStep(func=normalize, name='test')"
    panel.on_generation_finished(test_code)

    # Verify signal was emitted with correct code
    mock_handler.assert_called_once_with(test_code)
```

Run with: `pytest tests/gui/test_llm_code_generation.py -v`

### Findings

#### Existing Code Editor Infrastructure

The code editor (`QScintillaCodeEditorDialog` in `openhcs/pyqt_gui/services/simple_code_editor.py`) is used throughout OpenHCS for editing different types of code:

**Usage Contexts** (from codebase search):
1. **Pipeline Editor** (`pipeline_editor.py` line 717): `code_type='pipeline'`
2. **Plate Manager** (`plate_manager.py` line 1519): `code_type='orchestrator'`
3. **Step Parameter Editor** (`step_parameter_editor.py` line 551): `code_type='step'`
4. **Config Window** (`config_window.py` line 464): `code_type='config'`
5. **Function List Editor** (`function_list_editor.py` line 373): `code_type='function'`

**Existing Features** (lines 144-1036 in `simple_code_editor.py`):
- QScintilla-based Python editor with syntax highlighting
- Error handling (reopens editor at error line on failure)
- Save with Shift+Click support (keep window open)
- Clean mode toggle for different code types
- Menu bar with File/Edit/View menus
- Non-modal window (allows multiple editors open)
- Callback pattern for successful saves

**Integration Point**: By adding LLM panel directly to `QScintillaCodeEditorDialog`, we automatically get LLM assistance in ALL these contexts without any changes to calling code.

#### Code Editor UI Structure

Current button layout (line 222-234):
```python
button_layout = QHBoxLayout()

self.save_btn = QPushButton("Save")
self.save_btn.clicked.connect(self._on_save_clicked)
button_layout.addWidget(self.save_btn)

self.cancel_btn = QPushButton("Cancel")
self.cancel_btn.clicked.connect(self.reject)
button_layout.addWidget(self.cancel_btn)

button_layout.addStretch()
main_layout.addLayout(button_layout)
```

**Integration Point**: Add "LLM Assist" toggle button before Save button.

Current editor layout (line 219):
```python
main_layout.addWidget(self.editor)
```

**Integration Point**: Replace with QSplitter containing editor and LLM panel.

#### No Existing LLM Integration

Codebase search confirms no existing LLM integration. The only external service integrations are:
- ZMQ-based execution server (for remote pipeline execution)
- OMERO server (for microscopy data storage)
- Napari/Fiji (for visualization)

All use different patterns (ZMQ messaging, OMERO API, subprocess streaming), so we need a new HTTP-based service for LLM.

#### Example Pipeline Location

The example pipeline is at `openhcs/tests/basic_pipeline.py` (lines 18-85). This file contains a complete, working pipeline that demonstrates:
- All import patterns
- FunctionStep creation with various configurations
- Configuration usage (LazyProcessingConfig, LazyStepWellFilterConfig, etc.)
- Function chaining and parameter passing

This is the perfect reference to include in the LLM system prompt.

### Implementation Draft

**Status**: Ready for implementation after smell loop approval.

The plan above provides complete implementation details for all components:

1. **LLMPipelineService** (`openhcs/pyqt_gui/services/llm_pipeline_service.py`): Complete class with context-aware code generation
2. **LLMChatPanel** (`openhcs/pyqt_gui/widgets/llm_chat_panel.py`): Embeddable chat panel widget with signal-based communication
3. **Code Editor Integration** (`openhcs/pyqt_gui/services/simple_code_editor.py`): Exact line numbers and code changes to add LLM panel
4. **Dependencies**: Check/update `pyproject.toml` for `requests` library
5. **Testing**: Manual testing steps for all code contexts and integration test file

All code follows OpenHCS architectural principles:
- ✅ Stateless service class (LLMPipelineService)
- ✅ Fail-loud error handling (raises exceptions, shows error dialogs)
- ✅ No defensive programming (no hasattr, no silent failures)
- ✅ Consistent UI patterns (embeddable widgets, color scheme, style generator)
- ✅ Signal-based communication (Qt pattern)
- ✅ **Maximum code reuse**: Feature built into code editor itself, automatically works for ALL code editing contexts
- ✅ Context-aware: LLM knows what type of code is being edited (pipeline/step/config/function/orchestrator)

**Key Architectural Win**:
By integrating LLM directly into `QScintillaCodeEditorDialog`, we get LLM assistance in:
- Pipeline editor (when editing pipeline code)
- Step parameter editor (when editing step code)
- Config windows (when editing config code)
- Function list editor (when editing function patterns)
- Plate manager (when editing orchestrator code)

**All with ZERO changes to any calling code.** The feature is completely self-contained in the code editor service.


