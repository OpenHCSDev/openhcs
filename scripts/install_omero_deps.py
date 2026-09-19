#!/usr/bin/env python3
"""
Install ZeroC-Ice dependency for OMERO integration.

This script uses the shared zeroc_ice installer module from
openhcs.build_utils.zeroc_ice_installer to download and install
the appropriate zeroc-ice wheel from Glencoe Software's repository.

Usage:
    python scripts/install_omero_deps.py

After running this script, install openhcs with OMERO support:
    pip install 'openhcs[omero]'

For more information, see:
https://www.glencoesoftware.com/blog/2023/12/08/ice-binaries-for-omero.html
"""

import sys

# Import the shared zeroc_ice installer module
# This module is in openhcs/build_utils/zeroc_ice_installer.py
try:
    from openhcs.build_utils.zeroc_ice_installer import install_zeroc_ice
except ImportError:
    # If openhcs is not installed yet, try importing from build_utils
    import os

    sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
    from openhcs.build_utils.zeroc_ice_installer import install_zeroc_ice


def main() -> int:
    """
    Main installation function.

    Returns:
        Exit code (0 for success, 1 for failure)
    """
    print("=" * 70)
    print("ZeroC-Ice Installation Script for OMERO Integration")
    print("=" * 70)
    print()

    # Call the shared installation function
    success = install_zeroc_ice(verbose=True)

    if success:
        print()
        print("=" * 70)
        print("INSTALLATION SUCCESSFUL")
        print("=" * 70)
        print()
        print("You can now install openhcs with OMERO support:")
        print("  pip install 'openhcs[omero]'")
        print()
        print("Or use the requirements file:")
        print("  pip install -r requirements-omero.txt")
        print()
        return 0
    else:
        print()
        print("=" * 70)
        print("INSTALLATION FAILED")
        print("=" * 70)
        print()
        print("The installation failed. You can try manual installation:")
        print()
        print(
            "1. Download the wheel from: https://www.glencoesoftware.com/blog/2023/12/08/ice-binaries-for-omero.html"
        )
        print("2. Install manually: pip install /path/to/wheel")
        print()
        return 1


if __name__ == "__main__":
    sys.exit(main())
