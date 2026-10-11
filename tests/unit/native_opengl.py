"""Declared native OpenGL requirement for tests that render real Napari layers.

Napari's Qt viewer draws layers through vispy, which needs a current OpenGL
context. Qt's ``offscreen`` platform has none, so ``viewer.add_image`` fails
inside vispy and leaves a half-built canvas behind. CI's unit gate supplies
software OpenGL under Xvfb (integration-tests.yml, unit-tests job).
"""

from __future__ import annotations

import pytest


@pytest.fixture
def native_opengl(qapp) -> None:
    """Require a native OpenGL context; request it before creating a viewer."""

    from PyQt6.QtGui import QGuiApplication, QOffscreenSurface, QOpenGLContext

    surface = QOffscreenSurface()
    surface.create()
    context = QOpenGLContext()
    available = context.create() and context.makeCurrent(surface)
    if available:
        context.doneCurrent()
    surface.destroy()
    if not available:
        pytest.skip(
            "requires native OpenGL for Napari layer rendering; Qt platform "
            f"{QGuiApplication.platformName()!r} provides none (CI: xvfb + mesa)"
        )
