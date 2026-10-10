"""Microscopy dataset sources: vendor layouts, stores and their parsers.

Importing the package imports every module, so each handler, parser, store
adapter and metadata enricher registers in its kernel family. The kernel
imports this package only through ``Microscopy.extension_modules``.
"""

from importlib import import_module
from pkgutil import iter_modules

for _module_info in iter_modules(__path__):
    if not _module_info.name.startswith("_"):
        import_module(f"{__name__}.{_module_info.name}")
