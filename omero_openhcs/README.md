# OMERO-OpenHCS Plugin

OMERO.web plugin for OpenHCS GPU processing integration.

## Overview

This plugin adds OpenHCS processing capabilities to OMERO.web, allowing users to:
- Submit GPU processing pipelines from the browser
- Monitor job execution status
- View processing results

## Architecture

```
OMERO.web (Browser UI)
    ↓ HTTP/Django
OMERO.server (Data + Auth)
    ↓ ZeroMQ
OpenHCS Execution Server (GPU Processing)
```

## Installation

### 1. Install the plugin

```bash
pip install omero-openhcs
```

### 2. Configure OMERO.web

```bash
# Add to installed apps
omero config append omero.web.apps '"omero_openhcs"'

# Add to right panel plugins
omero config append omero.web.ui.right_plugins \
    '["OpenHCS", "omero_openhcs/webclient_plugins/right_plugin.js.html", "openhcs_panel"]'

# Restart OMERO.web
omero web restart
```

### 3. Start OpenHCS Execution Server

```bash
# On the OMERO server machine
python -m openhcs.runtime.zmq_execution_server_launcher \
    --port 7777 \
    --persistent
```

## Usage

1. **Browse to a Plate** in OMERO.web
2. **Click the "OpenHCS" tab** in the right panel
3. **Enter your pipeline code** in the editor
4. **Click "Submit"** to start processing
5. **Monitor status** in real-time
6. **View results** in OMERO.iviewer

## Example Pipeline

```python
from openhcs.processing.steps import FunctionStep
from openhcs.processing.gpu_functions import gaussian_filter, max_projection

pipeline_steps = [
    FunctionStep(func=gaussian_filter, sigma=2.0),
    FunctionStep(func=max_projection)
]
```

## Development

### Running locally

```bash
# Install in development mode
pip install -e .

# Configure OMERO.web
omero config append omero.web.apps '"omero_openhcs"'

# Start OMERO.web in development mode
omero web start --debug
```

## License

MIT License - see LICENSE file for details.
