"""OpenHCS config preview projections derived from config declarations."""

from typing import TYPE_CHECKING

from formbridge.utils.preview_formatters import check_enabled_field, resolve_preview_label

if TYPE_CHECKING:
    from openhcs.core.config import PartitionFilterConfig


def format_partition_filter_config(
    config: "PartitionFilterConfig",
    _config_attr: str,
) -> str | None:
    """Project one well-filter declaration into its compact preview text."""
    if not check_enabled_field(config):
        return None

    label = resolve_preview_label(config)
    if label is None:
        raise TypeError(f"{type(config).__name__} has no preview-label declaration")

    partition_filter = config.partition_filter
    if partition_filter is None:
        return label.label if config.show_preview_without_partition_filter else None

    if isinstance(partition_filter, list):
        well_display = str(len(partition_filter))
    else:
        well_display = str(partition_filter)

    return f"{label.label}{config.partition_filter_mode.preview_prefix}{well_display}"
