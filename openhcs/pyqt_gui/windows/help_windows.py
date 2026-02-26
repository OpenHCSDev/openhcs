"""PyQt6 help system - reuses Textual TUI help logic and components."""

import logging
from typing import Union, Callable, Optional
from PyQt6.QtWidgets import (
    QDialog,
    QVBoxLayout,
    QHBoxLayout,
    QPushButton,
    QLabel,
    QTextEdit,
    QScrollArea,
    QWidget,
    QMessageBox,
)
from PyQt6.QtCore import Qt

# REUSE the actual working Textual TUI help components
from openhcs.introspection import DocstringExtractor
from pyqt_reactive.theming import ColorScheme
from pyqt_reactive.theming import StyleSheetGenerator

logger = logging.getLogger(__name__)


class BaseHelpWindow(QDialog):
    """Base class for all PyQt6 help windows - reuses Textual TUI help logic."""

    def __init__(
        self,
        title: str = "Help",
        color_scheme: Optional[ColorScheme] = None,
        parent=None,
    ):
        super().__init__(parent)

        # Initialize color scheme and style generator
        self.color_scheme = color_scheme or ColorScheme()
        self.style_generator = StyleSheetGenerator(self.color_scheme)

        self.setWindowTitle(title)
        self.setModal(False)  # Allow interaction with main window

        # Setup UI
        self.setup_ui()

        # Apply centralized styling
        self.setStyleSheet(self.style_generator.generate_dialog_style())

    def setup_ui(self):
        """Setup the base help window UI."""
        layout = QVBoxLayout(self)

        # Content area (to be filled by subclasses)
        self.content_area = QScrollArea()
        self.content_area.setWidgetResizable(True)
        self.content_area.setVerticalScrollBarPolicy(
            Qt.ScrollBarPolicy.ScrollBarAsNeeded
        )
        self.content_area.setHorizontalScrollBarPolicy(
            Qt.ScrollBarPolicy.ScrollBarAsNeeded
        )
        layout.addWidget(self.content_area)

        # Close button
        button_layout = QHBoxLayout()
        button_layout.addStretch()

        close_btn = QPushButton("Close")
        close_btn.clicked.connect(self.close)
        button_layout.addWidget(close_btn)

        layout.addLayout(button_layout)


class DocstringHelpWindow(BaseHelpWindow):
    """Help window for functions and classes - reuses Textual TUI DocstringExtractor."""

    def __init__(
        self,
        target: Union[Callable, type],
        title: Optional[str] = None,
        color_scheme: Optional[ColorScheme] = None,
        parent=None,
    ):
        self.target = target

        # REUSE Textual TUI docstring extraction logic
        self.docstring_info = DocstringExtractor.extract(target)

        # Generate title from target if not provided
        if title is None:
            if hasattr(target, "__name__"):
                title = f"Help: {target.__name__}"
            else:
                title = "Help"

        super().__init__(title, color_scheme, parent)
        self.populate_content()

    def populate_content(self):
        """Populate the help content with minimal styling."""
        content_widget = QWidget()
        layout = QVBoxLayout(content_widget)
        layout.setContentsMargins(10, 10, 10, 10)
        layout.setSpacing(5)

        # Function/class summary
        if self.docstring_info.summary:
            summary_label = QLabel(self.docstring_info.summary)
            summary_label.setWordWrap(True)
            summary_label.setTextInteractionFlags(
                Qt.TextInteractionFlag.NoTextInteraction
            )
            summary_label.setStyleSheet(
                f"color: {self.color_scheme.to_hex(self.color_scheme.text_primary)}; font-size: 12px;"
            )
            layout.addWidget(summary_label)

        # Full description
        if self.docstring_info.description:
            desc_label = QLabel(self.docstring_info.description)
            desc_label.setWordWrap(True)
            desc_label.setTextInteractionFlags(Qt.TextInteractionFlag.NoTextInteraction)
            desc_label.setStyleSheet(
                f"color: {self.color_scheme.to_hex(self.color_scheme.text_primary)}; font-size: 12px;"
            )
            layout.addWidget(desc_label)

        # Parameters section
        if self.docstring_info.parameters:
            params_label = QLabel("Parameters:")
            params_label.setTextInteractionFlags(
                Qt.TextInteractionFlag.NoTextInteraction
            )
            params_label.setStyleSheet(
                f"color: {self.color_scheme.to_hex(self.color_scheme.text_accent)}; font-size: 14px; font-weight: bold; margin-top: 8px;"
            )
            layout.addWidget(params_label)

            for param_name, param_desc in self.docstring_info.parameters.items():
                # Parameter name
                name_label = QLabel(f"• {param_name}")
                name_label.setTextInteractionFlags(
                    Qt.TextInteractionFlag.NoTextInteraction
                )
                name_label.setStyleSheet(
                    f"color: {self.color_scheme.to_hex(self.color_scheme.text_primary)}; font-size: 12px; margin-left: 5px; margin-top: 3px;"
                )
                layout.addWidget(name_label)

                # Parameter description
                if param_desc:
                    desc_label = QLabel(param_desc)
                    desc_label.setWordWrap(True)
                    desc_label.setTextInteractionFlags(
                        Qt.TextInteractionFlag.NoTextInteraction
                    )
                    desc_label.setStyleSheet(
                        f"color: {self.color_scheme.to_hex(self.color_scheme.text_primary)}; font-size: 12px; margin-left: 20px;"
                    )
                    layout.addWidget(desc_label)

        # Returns section
        if self.docstring_info.returns:
            returns_label = QLabel("Returns:")
            returns_label.setTextInteractionFlags(
                Qt.TextInteractionFlag.NoTextInteraction
            )
            returns_label.setStyleSheet(
                f"color: {self.color_scheme.to_hex(self.color_scheme.text_accent)}; font-size: 14px; font-weight: bold; margin-top: 8px;"
            )
            layout.addWidget(returns_label)

            returns_desc = QLabel(self.docstring_info.returns)
            returns_desc.setWordWrap(True)
            returns_desc.setTextInteractionFlags(
                Qt.TextInteractionFlag.NoTextInteraction
            )
            returns_desc.setStyleSheet(
                f"color: {self.color_scheme.to_hex(self.color_scheme.text_primary)}; font-size: 12px; margin-left: 5px;"
            )
            layout.addWidget(returns_desc)

        # Examples section
        if self.docstring_info.examples:
            examples_label = QLabel("Examples:")
            examples_label.setTextInteractionFlags(
                Qt.TextInteractionFlag.NoTextInteraction
            )
            examples_label.setStyleSheet(
                f"color: {self.color_scheme.to_hex(self.color_scheme.text_accent)}; font-size: 14px; font-weight: bold; margin-top: 8px;"
            )
            layout.addWidget(examples_label)

            examples_text = QTextEdit()
            examples_text.setPlainText(self.docstring_info.examples)
            examples_text.setReadOnly(True)
            examples_text.setMaximumHeight(150)
            examples_text.setTextInteractionFlags(
                Qt.TextInteractionFlag.NoTextInteraction
            )
            examples_text.setStyleSheet(f"""
                QTextEdit {{
                    background-color: transparent;
                    color: {self.color_scheme.to_hex(self.color_scheme.text_primary)};
                    border: none;
                    font-family: monospace;
                    font-size: 11px;
                }}
                QTextEdit:hover {{
                    background-color: transparent;
                }}
            """)
            layout.addWidget(examples_text)

        layout.addStretch()
        self.content_area.setWidget(content_widget)

        # Auto-size to content
        self.adjustSize()
        # Set reasonable min/max sizes
        self.setMaximumSize(800, 600)


class HelpWindowManager:
    """PyQt6 help window manager - unified window for all help content."""

    # Class-level window reference for singleton behavior
    _help_window = None

    @classmethod
    def show_docstring_help(
        cls, target: Union[Callable, type], title: Optional[str] = None, parent=None
    ):
        """Show help for a function or class - reuses Textual TUI extraction logic."""
        try:
            # Check if existing window is still valid
            if cls._help_window and hasattr(cls._help_window, "isVisible"):
                try:
                    if not cls._help_window.isHidden():
                        cls._help_window.target = target
                        cls._help_window.docstring_info = DocstringExtractor.extract(
                            target
                        )
                        cls._help_window.setWindowTitle(
                            title or f"Help: {getattr(target, '__name__', 'Unknown')}"
                        )
                        cls._help_window.populate_content()
                        cls._help_window.raise_()
                        cls._help_window.activateWindow()
                        return
                except RuntimeError:
                    # Window was deleted, clear reference
                    cls._help_window = None

            # Create new window
            cls._help_window = DocstringHelpWindow(target, title=title, parent=parent)
            cls._help_window.show()

        except Exception as e:
            logger.error(f"Failed to show docstring help: {e}")
            QMessageBox.warning(parent, "Help Error", f"Failed to show help: {e}")

    @classmethod
    def show_parameter_help(
        cls,
        param_name: str,
        param_description: str,
        param_type: type = None,
        parent=None,
    ):
        """Show help for a parameter - creates a fake docstring object and uses DocstringHelpWindow."""
        try:
            # Create a fake docstring info object for the parameter
            from dataclasses import dataclass

            @dataclass
            class FakeDocstringInfo:
                summary: str = ""
                description: str = ""
                parameters: dict = None
                returns: str = ""
                examples: str = ""

            # Build parameter display
            type_str = (
                f" ({getattr(param_type, '__name__', str(param_type))})"
                if param_type
                else ""
            )
            fake_info = FakeDocstringInfo(
                summary=f"• {param_name}{type_str}",
                description=param_description or "No description available",
                parameters={},
                returns="",
                examples="",
            )

            # Check if existing window is still valid
            if cls._help_window and hasattr(cls._help_window, "isVisible"):
                try:
                    if not cls._help_window.isHidden():
                        cls._help_window.docstring_info = fake_info
                        cls._help_window.setWindowTitle(f"Parameter: {param_name}")
                        cls._help_window.populate_content()
                        cls._help_window.raise_()
                        cls._help_window.activateWindow()
                        return
                except RuntimeError:
                    # Window was deleted, clear reference
                    cls._help_window = None

            # Create new window with fake target
            class FakeTarget:
                __name__ = param_name

            cls._help_window = DocstringHelpWindow(
                FakeTarget, title=f"Parameter: {param_name}", parent=parent
            )
            cls._help_window.docstring_info = fake_info
            cls._help_window.populate_content()
            cls._help_window.show()

        except Exception as e:
            logger.error(f"Failed to show parameter help: {e}")
            QMessageBox.warning(parent, "Help Error", f"Failed to show help: {e}")


class HelpableWidget:
    """Mixin class to add help functionality to PyQt6 widgets - mirrors Textual TUI."""

    def show_function_help(self, target: Union[Callable, type]) -> None:
        """Show help window for a function or class."""
        HelpWindowManager.show_docstring_help(target, parent=self)

    def show_parameter_help(
        self, param_name: str, param_description: str, param_type: type = None
    ) -> None:
        """Show help window for a parameter."""
        HelpWindowManager.show_parameter_help(
            param_name, param_description, param_type, parent=self
        )
