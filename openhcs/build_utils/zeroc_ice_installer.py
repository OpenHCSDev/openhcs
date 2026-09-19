"""
Shared ZeroC-Ice installation utilities for openhcs.

This module provides functions to download and install ZeroC-Ice
from Glencoe Software's repository, which is required for OMERO
integration but not available on PyPI.

This module is used by:
- Build hooks (for automatic installation during pip install)
- The install_omero_deps.py script (for manual installation)

For more information, see:
https://www.glencoesoftware.com/blog/2023/12/08/ice-binaries-for-omero.html
"""

import sys
import platform
import urllib.request
import urllib.error
import subprocess
from pathlib import Path
from typing import Optional

# ZeroC-Ice wheel URL configuration
ZEROC_ICE_BASE_URL = "https://downloads.openmicroscopy.org/ice/"
ZEROC_ICE_VERSION = "3.7.9"

# Supported Python versions
SUPPORTED_PYTHON_VERSIONS = ["3.11", "3.12"]


def get_python_version() -> str:
    """
    Get current Python version (e.g., '3.11', '3.12').

    Returns:
        Python version as string
    """
    return f"{sys.version_info.major}.{sys.version_info.minor}"


def get_platform() -> str:
    """
    Get current platform identifier.

    Returns:
        Platform name: 'windows', 'linux', or 'macos'

    Raises:
        RuntimeError: If the platform is not supported
    """
    system = platform.system().lower()
    if system == "windows":
        return "windows"
    elif system == "darwin":
        return "macos"
    elif system == "linux":
        return "linux"
    else:
        raise RuntimeError(f"Unsupported platform: {system}")


def get_wheel_url(python_version: str, platform_name: str) -> str:
    """
    Construct the zeroc-ice wheel URL for the given Python version and platform.

    Args:
        python_version: Python version (e.g., '3.11', '3.12')
        platform_name: Platform name ('windows', 'linux', 'macos')

    Returns:
        URL to the appropriate zeroc-ice wheel
    """
    # Glencoe Software provides zeroc-ice wheels for Python 3.11 and 3.12
    # The URL pattern: https://downloads.openmicroscopy.org/ice/python-{version}/zeroc_ice-{version}-py3-none-any.whl
    url = f"{ZEROC_ICE_BASE_URL}python-{python_version}/zeroc_ice-{ZEROC_ICE_VERSION}-py3-none-any.whl"
    return url


def download_wheel(url: str, dest_dir: Path, verbose: bool = True) -> Optional[Path]:
    """
    Download a wheel file from the given URL.

    Args:
        url: URL to download from
        dest_dir: Directory to save the wheel file
        verbose: Whether to print progress messages

    Returns:
        Path to the downloaded wheel file, or None if download failed
    """
    try:
        dest_dir.mkdir(parents=True, exist_ok=True)
        filename = url.split("/")[-1]
        dest_path = dest_dir / filename

        if verbose:
            print(f"[openhcs] Downloading {url}...")
        urllib.request.urlretrieve(url, dest_path)
        if verbose:
            print(f"[openhcs] Downloaded to {dest_path}")
        return dest_path
    except urllib.error.URLError as e:
        if verbose:
            print(f"[openhcs] Failed to download: {e}")
        return None


def install_wheel(wheel_path: Path, verbose: bool = True) -> bool:
    """
    Install a wheel file using pip.

    Args:
        wheel_path: Path to the wheel file
        verbose: Whether to print progress messages

    Returns:
        True if installation succeeded, False otherwise
    """
    try:
        result = subprocess.run(
            [sys.executable, "-m", "pip", "install", str(wheel_path)],
            check=True,
            capture_output=True,
            text=True,
        )
        if verbose:
            print("[openhcs] Successfully installed zeroc-ice!")
        return True
    except subprocess.CalledProcessError as e:
        if verbose:
            print(f"[openhcs] Failed to install wheel: {e}")
        return False


def verify_installation(verbose: bool = True) -> bool:
    """
    Verify that zeroc-ice is installed and importable.

    Args:
        verbose: Whether to print progress messages

    Returns:
        True if zeroc-ice is installed, False otherwise
    """
    try:
        import Ice

        if verbose:
            print(
                f"[openhcs] zeroc-ice is already installed (Ice version: {Ice.stringVersion()})"
            )
        return True
    except ImportError:
        return False


def install_zeroc_ice(verbose: bool = True, dest_dir: Optional[Path] = None) -> bool:
    """
    Install zeroc-ice from Glencoe Software's repository.

    This function detects the current Python version and platform,
    downloads the appropriate wheel, and installs it.

    Args:
        verbose: Whether to print progress messages
        dest_dir: Directory to save the wheel file (defaults to ~/.openhcs/wheels)

    Returns:
        True if installation succeeded or already installed, False otherwise
    """
    # Check if already installed
    if verify_installation(verbose=verbose):
        return True

    # Get system information
    python_version = get_python_version()
    platform_name = get_platform()

    if verbose:
        print(f"[openhcs] Python version: {python_version}")
        print(f"[openhcs] Platform: {platform_name}")

    # Validate Python version
    if python_version not in SUPPORTED_PYTHON_VERSIONS:
        if verbose:
            print(
                f"[openhcs] Warning: Python {python_version} may not have a pre-built zeroc-ice wheel."
            )
            print(
                f"[openhcs] Supported versions: {', '.join(SUPPORTED_PYTHON_VERSIONS)}"
            )
            print(f"[openhcs] Continuing anyway...")

    # Get wheel URL
    wheel_url = get_wheel_url(python_version, platform_name)
    if verbose:
        print(f"[openhcs] Wheel URL: {wheel_url}")

    # Set destination directory
    if dest_dir is None:
        dest_dir = Path.home() / ".openhcs" / "wheels"

    # Download wheel
    wheel_path = download_wheel(wheel_url, dest_dir, verbose=verbose)

    if wheel_path is None:
        if verbose:
            print(
                "[openhcs] Download failed. zeroc-ice will not be installed automatically."
            )
            print(
                "[openhcs] Please install manually: python scripts/install_omero_deps.py"
            )
        return False

    # Install wheel
    if verbose:
        print("[openhcs] Installing zeroc-ice...")
    if not install_wheel(wheel_path, verbose=verbose):
        if verbose:
            print(
                "[openhcs] Installation failed. Please install manually: python scripts/install_omero_deps.py"
            )
        return False

    if verbose:
        print("[openhcs] zeroc-ice installation complete!")
    return True
