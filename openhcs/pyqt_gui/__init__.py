"""
OpenHCS PyQt6 GUI Implementation

Complete PyQt6 migration of the OpenHCS Textual TUI with full feature parity.
Provides native desktop integration while preserving all existing functionality.
"""

import sys
import logging

# CRITICAL: Check for SILENT mode BEFORE any OpenHCS imports
# This must be at MODULE LEVEL to run before main.py is imported
if '--log-level' in sys.argv:
    log_level_idx = sys.argv.index('--log-level')
    if log_level_idx + 1 < len(sys.argv) and sys.argv[log_level_idx + 1] == 'SILENT':
        # Disable ALL logging before any imports
        logging.disable(logging.CRITICAL)
        root_logger = logging.getLogger()
        root_logger.setLevel(logging.CRITICAL + 1)

__version__ = "1.0.0"
__author__ = "OpenHCS Development Team"

# Lazy-load GUI classes to support environment-specific Qt platform initialization.
# The OpenHCS GUI requires platform-specific Qt configuration (WSL2 needs Wayland,
# macOS needs Cocoa plugin path, etc.) before PyQt6 is imported. This configuration
# happens in launch.py:setup_qt_platform(). Lazy loading via __getattr__ ensures that
# GUI imports are deferred until after platform setup completes.

def __getattr__(name: str):
    """Lazy import GUI classes to defer PyQt6 initialization.
    
    Defers importing OpenHCSMainWindow and OpenHCSPyQtApp until accessed,
    allowing launch.py:setup_qt_platform() to configure Qt before any
    PyQt6 libraries are loaded.
    
    Args:
        name: The attribute being accessed.
        
    Returns:
        The requested class.
        
    Raises:
        AttributeError: If the requested attribute doesn't exist.
    """
    if name == "OpenHCSMainWindow":
        from openhcs.pyqt_gui.main import OpenHCSMainWindow
        return OpenHCSMainWindow
    elif name == "OpenHCSPyQtApp":
        from openhcs.pyqt_gui.app import OpenHCSPyQtApp
        return OpenHCSPyQtApp
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")

__all__ = [
    "OpenHCSMainWindow",
    "OpenHCSPyQtApp"
]
