"""Real source-binding declarations use the shared bounded preview policy."""

from dataclasses import replace

from openhcs.core.config import SourceBindingsConfig
from openhcs.core.source_bindings import NamedSourceBinding
from openhcs.pyqt_gui.config import UIConfig
from pyqt_reactive.utils.preview_formatters import (
    PreviewFieldFormatRequest,
    PreviewValueDetail,
)
from pyqt_reactive.widgets.shared.manager_preview_formatting import (
    ManagerPreviewFieldFormatter,
)


def test_source_binding_collection_is_compact_and_expansion_preserves_its_scope():
    sources = SourceBindingsConfig(
        bindings=(
            NamedSourceBinding(alias="neurons"),
            NamedSourceBinding(alias="nuclei"),
        )
    )
    policy = UIConfig().list_previews
    formatter = ManagerPreviewFieldFormatter()
    request = PreviewFieldFormatRequest(
        field_path="source_bindings_config.bindings",
        value=sources.bindings,
        field_owner=SourceBindingsConfig,
        value_formatter=policy.format_value,
    )
    assert formatter.format_field(request) == "bindings:[2]"
    expanded = replace(
        policy, collection_detail=PreviewValueDetail.EXPANDED, max_value_length=0
    )
    expanded_request = replace(request, value_formatter=expanded.format_value)
    label = formatter.format_field(expanded_request)
    assert "neurons" in label and "nuclei" in label
    assert expanded_request.value is sources.bindings
    assert expanded_request.field_path == request.field_path
