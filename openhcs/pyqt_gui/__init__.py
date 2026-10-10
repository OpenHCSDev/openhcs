"""OpenHCS PyQt desktop application."""

import logging
import sys

# CRITICAL: Check for SILENT mode BEFORE any OpenHCS imports
# This must be at MODULE LEVEL to run before main.py is imported
if "--log-level" in sys.argv:
    log_level_idx = sys.argv.index("--log-level")
    if log_level_idx + 1 < len(sys.argv) and sys.argv[log_level_idx + 1] == "SILENT":
        # Disable ALL logging before any imports
        logging.disable(logging.CRITICAL)
        root_logger = logging.getLogger()
        root_logger.setLevel(logging.CRITICAL + 1)

from python_introspect import lazy_exports  # noqa: E402

__all__ = lazy_exports(
    globals(),
    {
        "openhcs.pyqt_gui.main": ("OpenHCSMainWindow",),
        "openhcs.pyqt_gui.app": ("OpenHCSPyQtApp",),
    },
)
