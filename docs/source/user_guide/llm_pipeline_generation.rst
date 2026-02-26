===========================
LLM Pipeline Generation
===========================

*Module: openhcs.pyqt_gui.services.llm_pipeline_service*  
*Status: EXPERIMENTAL*

---

Overview
========

The LLM Pipeline Service enables natural language pipeline generation using local or remote LLM endpoints. Users describe their analysis workflow in plain English, and the LLM generates executable OpenHCS pipeline code.

Quick Reference
===============

.. code-block:: python

    from openhcs.pyqt_gui.services.llm_pipeline_service import LLMPipelineService
    
    # Initialize service (default: local Ollama)
    service = LLMPipelineService(
        api_endpoint="http://localhost:11434/api/generate",
        model="qwen2.5-coder:32b"
    )
    
    # Generate pipeline from natural language
    user_request = "Create a pipeline that applies Gaussian blur and detects cells"
    
    pipeline_code = service.generate_pipeline(user_request)
    
    # Execute generated code
    exec(pipeline_code)

Ollama Endpoint Configuration
==============================

Local Ollama Setup
------------------

.. code-block:: bash

    # Install Ollama
    curl -fsSL https://ollama.com/install.sh | sh
    
    # Pull recommended model
    ollama pull qwen2.5-coder:32b
    
    # Start Ollama server (runs on port 11434 by default)
    ollama serve

**Recommended models**:

- ``qwen2.5-coder:32b``: Best code generation quality
- ``qwen2.5-coder:14b``: Faster, good quality
- ``codellama:13b``: Alternative option

Remote Ollama Setup
-------------------

.. code-block:: python

    # Connect to remote Ollama instance
    service = LLMPipelineService(
        api_endpoint="http://remote-server:11434/api/generate",
        model="qwen2.5-coder:32b"
    )

**Network requirements**:

- Port 11434 must be accessible
- Firewall rules configured for remote access
- Low latency recommended (< 100ms)

Custom LLM Endpoints
--------------------

.. code-block:: python

    # OpenAI-compatible endpoint
    service = LLMPipelineService(
        api_endpoint="https://api.openai.com/v1/completions",
        model="gpt-4"
    )
    
    # Custom endpoint with authentication
    service = LLMPipelineService(
        api_endpoint="https://custom-llm.example.com/generate",
        model="custom-model"
    )
    service.set_auth_header("Bearer", "your-api-key")

LLMPipelineService Contract
============================

Service Interface
-----------------

.. code-block:: python

    class LLMPipelineService:
        """Service for generating OpenHCS pipelines using LLM."""
        
        def __init__(self, api_endpoint: str, model: str):
            """Initialize LLM service.
            
            Args:
                api_endpoint: LLM API endpoint URL
                model: Model name to use for generation
            """
            self.api_endpoint = api_endpoint
            self.model = model
            self.system_prompt = self._build_system_prompt()
        
        def generate_pipeline(self, user_request: str) -> str:
            """Generate pipeline code from natural language request.
            
            Args:
                user_request: Natural language description of pipeline
            
            Returns:
                Executable Python code for OpenHCS pipeline
            
            Raises:
                LLMServiceError: If generation fails
            """
            pass
        
        def _build_system_prompt(self) -> str:
            """Build comprehensive system prompt with OpenHCS documentation."""
            pass

Request/Response Format
-----------------------

.. code-block:: python

    # Request format (Ollama API)
    request = {
        "model": "qwen2.5-coder:32b",
        "prompt": user_request,
        "system": system_prompt,
        "stream": False,
        "options": {
            "temperature": 0.2,  # Low temperature for code generation
            "top_p": 0.9,
            "max_tokens": 2048
        }
    }
    
    # Response format
    response = {
        "model": "qwen2.5-coder:32b",
        "created_at": "2025-01-15T10:30:00Z",
        "response": "# Generated pipeline code\n...",
        "done": True
    }

System Prompt Construction
===========================

The system prompt provides comprehensive OpenHCS context to the LLM:

.. code-block:: python

    def _build_system_prompt(self) -> str:
        """Build system prompt with OpenHCS documentation."""
        
        # Load example pipeline
        example_pipeline = self._load_example_pipeline()
        
        # Load function library documentation
        function_docs = self._load_function_docs()
        
        # Construct prompt
        prompt = f"""
        You are an expert OpenHCS pipeline generator.
        
        OpenHCS is a high-content screening image processing engine.
        
        ## Example Pipeline
        {example_pipeline}
        
        ## Available Functions
        {function_docs}
        
        ## Guidelines
        - Use FunctionStep for each processing operation
        - Specify function name and parameters
        - Use appropriate memory decorators (@numpy, @cupy, @pyclesperanto)
        - Include materialization for final outputs
        
        Generate executable Python code that creates an OpenHCS pipeline.
        """
        
        return prompt

    def get_system_prompt(self, code_type: str = "pipeline") -> str:
        """Return the runtime-generated system prompt for a given context.
        
        Args:
            code_type: Type of code being generated ("pipeline" or "function")
            
        Returns:
            System prompt tailored for the specific code type
        """
        if code_type == "function":
            return self._system_prompts.get("function", self.system_prompt)
        return self._system_prompts.get("pipeline", self.system_prompt)

**System prompt components**:

1. **Example pipeline**: Working OpenHCS pipeline code
2. **Function library**: Available processing functions and signatures
3. **Guidelines**: Best practices for pipeline construction
4. **API documentation**: Core classes and patterns
5. **Context-aware prompts**: Different prompts for pipeline vs function generation

Array Backend Handling
----------------------

The LLM now understands OpenHCS memory decorators and handles array backends automatically:

**Memory Decorators**:

- ``@numpy`` - Function accepts and returns NumPy arrays
- ``@cupy`` - Function accepts and returns CuPy GPU arrays  
- ``@pyclesperanto`` - Function accepts and returns pyclesperanto GPU arrays

**Key Rules for Generated Functions**:

1. **First parameter MUST be named 'image'** - 3D array in (C, Y, X) a.k.a. (Z, Y, X) format
2. **Accept the decorator's declared input type** - Don't manually convert between backends
3. **Return the declared output type** - OpenHCS handles cross-step conversions automatically
4. **No manual backend conversions** - Don't use ``cp.asnumpy()``, ``cle.pull()``, etc.
5. **Decorator adds keyword-only args** - ``slice_by_slice`` and ``dtype_conversion`` (defaults to preserving input dtype)

**Example Function Generation**:

.. code-block:: python

    # CuPy function - no manual conversion needed
    @cupy
    def count_cells_cupy(image, min_area=50):
        import cupy as cp
        from cucim.skimage import measure
        
        labeled = measure.label(image > 0)
        regions = measure.regionprops(labeled, intensity_image=image)
        
        stats_list = []
        masks = []
        for props in regions:
            if props.area >= min_area:
                stats_list.append({
                    'area': int(props.area),
                    'centroid': tuple(props.centroid)
                })
                masks.append(labeled == props.label)
        
        return image, stats_list, masks  # Return CuPy array directly

**Important**: The function returns the CuPy array directly. OpenHCS automatically handles
conversions between steps with different memory decorators.

Chat Panel Integration
======================

The chat panel provides a conversational interface for pipeline generation:

.. code-block:: python

    from openhcs.pyqt_gui.widgets.llm_chat_panel import LLMChatPanel
    
    # Create chat panel
    chat_panel = LLMChatPanel(llm_service=service)
    
    # User sends message
    chat_panel.send_message("Create a pipeline for cell counting")
    
    # LLM responds with generated code
    # User can refine request or execute code

Chat Panel Features
-------------------

- **Conversational refinement**: Iteratively improve generated pipelines
- **Code preview**: View generated code before execution
- **Error feedback**: LLM can fix errors based on execution results
- **History**: Review previous generations and requests

Editor Toggle Integration
--------------------------

The chat panel integrates with the code editor toggle:

.. code-block:: python

    from openhcs.pyqt_gui.services.simple_code_editor import SimpleCodeEditor
    
    class SimpleCodeEditor(QWidget):
        def __init__(self):
            # Create editor
            self.code_editor = QTextEdit()
            
            # Create chat panel
            self.chat_panel = LLMChatPanel(llm_service=service)
            
            # Create toggle button
            self.toggle_button = QPushButton("Show Chat")
            self.toggle_button.clicked.connect(self._toggle_chat)
        
        def _toggle_chat(self):
            """Toggle between code editor and chat panel."""
            if self.chat_panel.isVisible():
                self.chat_panel.hide()
                self.code_editor.show()
                self.toggle_button.setText("Show Chat")
            else:
                self.code_editor.hide()
                self.chat_panel.show()
                self.toggle_button.setText("Show Editor")

**Key insight**: Users can switch between manual code editing and LLM-assisted generation without losing context.

Common Patterns
===============

Basic Pipeline Generation
--------------------------

.. code-block:: python

    # Initialize service
    service = LLMPipelineService()
    
    # Generate pipeline
    request = "Apply Gaussian blur with sigma=2.0, then threshold at 0.5"
    code = service.generate_pipeline(request)
    
    # Execute
    exec(code)

Iterative Refinement
--------------------

.. code-block:: python

    # Initial request
    code_v1 = service.generate_pipeline("Detect cells")
    
    # Refine based on results
    code_v2 = service.generate_pipeline(
        "Detect cells, but use Voronoi-Otsu method instead of thresholding"
    )
    
    # Further refinement
    code_v3 = service.generate_pipeline(
        "Detect cells with Voronoi-Otsu, filter cells smaller than 50 pixels"
    )

Error-Driven Refinement
------------------------

.. code-block:: python

    # Generate pipeline
    code = service.generate_pipeline("Process images")
    
    # Execute and catch errors
    try:
        exec(code)
    except Exception as e:
        # Ask LLM to fix error
        fixed_code = service.generate_pipeline(
            f"Fix this error: {e}\n\nOriginal code:\n{code}"
        )
        exec(fixed_code)

Implementation Notes
====================

**🔬 Source Code**: 

- Service: ``openhcs/pyqt_gui/services/llm_pipeline_service.py`` (line 1)
- Chat panel: ``openhcs/pyqt_gui/widgets/llm_chat_panel.py`` (line 1)
- Editor integration: ``openhcs/pyqt_gui/services/simple_code_editor.py`` (line 203)

**🏗️ Architecture**: 

- :doc:`../architecture/pipeline-compilation-system` - Pipeline architecture
- :doc:`code_ui_editing` - Code editor integration

**📊 Performance**: 

- Generation time: 5-30 seconds (depends on model and hardware)
- Local Ollama: Faster, no network latency
- Remote endpoints: Slower, network-dependent

Key Design Decisions
====================

**Why Ollama as default?**

Ollama provides local LLM execution without API costs or privacy concerns. Users control their own models.

**Why include example pipeline in system prompt?**

Examples provide concrete patterns for the LLM to follow, improving code quality and reducing errors.

**Why integrate with code editor toggle?**

Users can seamlessly switch between manual editing and LLM assistance, combining human expertise with AI generation.

Common Gotchas
==============

- **Ollama must be running**: Service fails if Ollama server is not accessible
- **Model must be pulled**: ``ollama pull <model>`` required before first use
- **Generated code may need refinement**: LLM output is not guaranteed to be correct
- **System prompt affects quality**: Better documentation in prompt → better generated code
- **Temperature affects creativity**: Lower temperature (0.2) for code, higher (0.7) for explanations

Debugging LLM Issues
====================

Symptom: Connection Refused
----------------------------

**Cause**: Ollama server not running

**Diagnosis**:

.. code-block:: bash

    # Check if Ollama is running
    curl http://localhost:11434/api/tags

**Fix**: Start Ollama server:

.. code-block:: bash

    ollama serve

Symptom: Poor Code Quality
---------------------------

**Cause**: Insufficient context in system prompt

**Diagnosis**: Review generated code for common errors

**Fix**: Enhance system prompt with more examples and documentation

Symptom: Slow Generation
-------------------------

**Cause**: Large model or remote endpoint

**Diagnosis**: Measure generation time

**Fix**: Use smaller model or local Ollama instance

Advanced Usage
==============

Custom System Prompt
--------------------

.. code-block:: python

    class CustomLLMService(LLMPipelineService):
        def _build_system_prompt(self):
            """Custom system prompt with domain-specific examples."""
            return """
            You are an expert in neuroscience image analysis.
            
            Generate OpenHCS pipelines for neurite analysis, cell counting,
            and synaptic puncta detection.
            
            [Custom examples and documentation]
            """

Streaming Responses
-------------------

.. code-block:: python

    def generate_pipeline_streaming(self, user_request: str):
        """Generate pipeline with streaming response."""
        request = {
            "model": self.model,
            "prompt": user_request,
            "system": self.system_prompt,
            "stream": True  # Enable streaming
        }
        
        response = requests.post(self.api_endpoint, json=request, stream=True)
        
        for line in response.iter_lines():
            if line:
                chunk = json.loads(line)
                yield chunk['response']

