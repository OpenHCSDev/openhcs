"""The source-binding editor preserves every field of the bindings it edits."""

from __future__ import annotations

from dataclasses import replace

from PyQt6.QtWidgets import QCheckBox

from openhcs.core.config import StepSourceBindingsConfig
from openhcs.core.source_bindings import (
    ComponentSelector,
    ImagePlaneSource,
    NamedSourceBinding,
    SourceSelector,
)
from openhcs.pyqt_gui.widgets.source_bindings_editor import SourceBindingsEditorWidget
from openhcs.domains.microscopy.axes import Microscopy


def binding_with_unlisted_fields() -> NamedSourceBinding:
    return NamedSourceBinding(
        alias="DNA",
        selector=SourceSelector(
            components=(ComponentSelector(Microscopy.Channel, "1"),),
        ),
        explicit_source=ImagePlaneSource(uri="/data/plate/dna.tif", series="0"),
        load_as_monochrome=True,
        load_as_mask=True,
        source_channel_axis=0,
        source_channel_counts=frozenset({3}),
    )


def test_bindings_table_round_trip_preserves_every_binding_field(qapp) -> None:
    binding = binding_with_unlisted_fields()
    widget = SourceBindingsEditorWidget.from_bindings(
        StepSourceBindingsConfig(enabled=True, bindings=(binding,))
    )
    dialog = widget._create_step_bindings_dialog()
    editor = dialog.editor
    try:
        assert dialog.bindings() == (binding,)

        editor.table.item(*editor.cell_position(0, "alias")).setText("Nuclei")
        editor.table.cellWidget(*editor.cell_position(0, "components")).set_value(
            (ComponentSelector(Microscopy.Channel, "2"),)
        )
        mask_checkbox = editor.table.cellWidget(*editor.cell_position(0, "load_as_mask"))
        assert isinstance(mask_checkbox, QCheckBox)
        mask_checkbox.setChecked(False)

        expected = replace(
            binding,
            alias="Nuclei",
            selector=replace(
                binding.selector,
                components=(ComponentSelector(Microscopy.Channel, "2"),),
            ),
            load_as_mask=False,
        )
        assert dialog.bindings() == (expected,)

        widget._apply_step_bindings(dialog.bindings())
        assert widget.get_value().bindings == (expected,)
    finally:
        dialog.deleteLater()
        widget.deleteLater()
