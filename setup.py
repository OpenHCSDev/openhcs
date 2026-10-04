"""Setuptools build hooks for projecting OpenHCS MCP knowledge resources.

Dependency and package metadata comes exclusively from ``pyproject.toml``.
"""

import os
import runpy
import shutil
from abc import ABC, abstractmethod
from pathlib import Path

from setuptools import Extension, setup
from setuptools.command.build_ext import build_ext as _build_ext
from setuptools.command.build_py import build_py as _build_py
from setuptools.command.sdist import sdist as _sdist

_KNOWLEDGE_BUILD_HELPERS = runpy.run_path(
    str(Path(__file__).resolve().parent / "scripts/build_mcp_knowledge_assets.py")
)
KNOWLEDGE_MANIFEST_RELATIVE_PATH = _KNOWLEDGE_BUILD_HELPERS[
    "KNOWLEDGE_MANIFEST_RELATIVE_PATH"
]
PACKAGED_KNOWLEDGE_ROOT_RELATIVE_PATH = _KNOWLEDGE_BUILD_HELPERS[
    "PACKAGED_KNOWLEDGE_ROOT_RELATIVE_PATH"
]
project_knowledge_assets = _KNOWLEDGE_BUILD_HELPERS["project_knowledge_assets"]


class BuildPyWithMcpKnowledge(_build_py):
    """Project a fresh OpenHCS package and its canonical MCP knowledge assets."""

    def run(self):
        package_build_root = Path(self.build_lib) / "openhcs"
        if package_build_root.exists():
            shutil.rmtree(package_build_root)
        super().run()
        project_root = Path(__file__).resolve().parent
        if (project_root / KNOWLEDGE_MANIFEST_RELATIVE_PATH).is_file():
            project_knowledge_assets(
                project_root,
                Path(self.build_lib) / PACKAGED_KNOWLEDGE_ROOT_RELATIVE_PATH,
            )


class SdistWithMcpKnowledge(_sdist):
    """Include projected MCP knowledge resources in source distributions."""

    def make_release_tree(self, base_dir, files):
        super().make_release_tree(base_dir, files)
        project_knowledge_assets(
            Path(__file__).resolve().parent,
            Path(base_dir) / PACKAGED_KNOWLEDGE_ROOT_RELATIVE_PATH,
        )


class OpenHCSNativeExtension(Extension, ABC):
    """Build native module declarations with one stable-ABI compiler policy."""

    @property
    @abstractmethod
    def qualified_module_name(self) -> str:
        """Declare the native module; its qualified name also owns its source path."""

    def __init__(self) -> None:
        module_name = self.qualified_module_name
        source_path = Path(*module_name.split(".")).with_suffix(".cpp")
        super().__init__(
            module_name,
            sources=[source_path.as_posix()],
            language="c++",
            define_macros=[("Py_LIMITED_API", "0x030B0000")],
            py_limited_api=True,
            extra_compile_args=["/O2"] if os.name == "nt" else ["-O3"],
        )

    def prepare_build_sources(self, build_root: Path) -> None:
        """Prepare any generated sources at the native package-build boundary."""

    @classmethod
    def declared_extensions(cls) -> list[Extension]:
        """Derive compilation targets from concrete declarations in this family."""
        return [declaration() for declaration in cls.__subclasses__()]


class GranularityNativeExtension(OpenHCSNativeExtension):
    @property
    def qualified_module_name(self) -> str:
        return "openhcs.processing.backends.cellprofiler._granularity_native"


class TabularNativeExtension(OpenHCSNativeExtension):
    @property
    def qualified_module_name(self) -> str:
        return "openhcs.core._tabular_native"


class MedianNativeExtension(OpenHCSNativeExtension):
    @property
    def qualified_module_name(self) -> str:
        return "openhcs.processing.backends.cellprofiler._median_native"

    def prepare_build_sources(self, build_root: Path) -> None:
        generator = runpy.run_path(
            str(Path(__file__).resolve().parent / "scripts/build_median_network.py")
        )
        generated_root = build_root / "median-network"
        generator["build_median_network_header"](
            generated_root / "_median_network_generated.h"
        )
        self.include_dirs.append(str(generated_root.resolve()))
        self.depends.extend([
            str(Path(__file__).resolve().parent / "scripts/build_median_network.py"),
            str(generated_root / "_median_network_generated.h"),
        ])


class BuildNativeExtensions(_build_ext):
    """Prepare declared native sources without executing runtime compilation."""

    def build_extension(self, extension):
        extension.prepare_build_sources(Path(self.build_temp))
        super().build_extension(extension)


setup(
    ext_modules=OpenHCSNativeExtension.declared_extensions(),
    cmdclass={
        "build_ext": BuildNativeExtensions,
        "build_py": BuildPyWithMcpKnowledge,
        "sdist": SdistWithMcpKnowledge,
    },
)
