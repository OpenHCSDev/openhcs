"""Unit-suite process setup."""

import pytest

from openhcs.utils.environment import OpenHCSProcessEnvironment

if not OpenHCSProcessEnvironment.cpu_only_mode():

    @pytest.fixture(scope="session", autouse=True)
    def session_qapplication(qapp):
        """Create the unit session's one QApplication before any test runs.

        A process holds one Qt application. In-process MCP transports adopt an
        existing one and otherwise create a QCoreApplication, after which no
        later unit test could create a widget.
        """
        yield qapp
