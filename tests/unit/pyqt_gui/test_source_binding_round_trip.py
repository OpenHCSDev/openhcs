"""The source-binding editor preserves every field of the bindings it edits."""

from __future__ import annotations

from dataclasses import replace

from openhcs.core.config import StepSourceBindingsConfig
from openhcs.core.source_bindings import (
    ComponentSelector,
    ImagePlaneSource,
    NamedSourceBinding,
    SourceSelector,
)
from openhcs.constants.constants import AllComponents
from openhcs.pyqt_gui.widgets.source_bindings_editor import SourceBindingsEditorWidget


def binding_with_unlisted_fields() -> NamedSourceBinding:
    return NamedSourceBinding(
        alias="DNA",
        selector=SourceSelector(
            components=(ComponentSelector(AllComponents.CHANNEL, "1"),),
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
    try:
        assert dialog.bindings() == (binding,)

        alias_row = next(
            row
            for row in range(dialog.editor.table.rowCount())
            if dialog.editor.table.verticalHeaderItem(row).text() == "Alias"
        )
        dialog.editor.table.item(alias_row, 0).setText("Nuclei")

        assert dialog.bindings() == (replace(binding, alias="Nuclei"),)
    finally:
        dialog.deleteLater()
        widget.deleteLater()
