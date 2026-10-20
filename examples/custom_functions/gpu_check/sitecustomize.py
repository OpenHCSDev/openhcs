"""Activate the conversion trace in every Python process that has this directory on PYTHONPATH.

Python imports ``sitecustomize`` at start-up. The OpenHCS execution server and
its workers are separate processes, so this is how the diagnostic reaches them
without changing OpenHCS. It does nothing unless ``OPENHCS_CONVERSION_TRACE``
names a file.
"""

import os

if os.environ.get("OPENHCS_CONVERSION_TRACE"):
    import conversion_trace

    conversion_trace.install()
