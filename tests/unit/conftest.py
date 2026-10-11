"""Unit-suite process setup."""

import pytest


@pytest.fixture(scope="session", autouse=True)
def session_qapplication(request):
    """Create the unit session's one QApplication before any test runs.

    A process holds one Qt application. In-process MCP transports adopt an
    existing one and otherwise create a QCoreApplication, after which no later
    unit test could create a widget. Sessions without pytest-qt (CPU-only, or a
    narrowed ``--confcutdir``) run no widget tests.
    """
    if request.config.pluginmanager.hasplugin("pytestqt"):
        request.getfixturevalue("qapp")
