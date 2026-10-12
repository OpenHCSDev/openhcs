"""Declaration-driven OpenHCS config preview projections."""

from formbridge.utils.preview_formatters import resolve_preview_label

from openhcs.core.config import (
    LazyNapariStreamingConfig,
    LazyPartitionFilterConfig,
    NapariStreamingConfig,
    StepMaterializationConfig,
    PartitionFilterConfig,
)
from openhcs.pyqt_gui.widgets.config_preview_formatters import (
    format_partition_filter_config,
)
from openhcs.core.config import ExcludePartitions


def test_partition_filter_preview_label_is_owned_by_config_declaration() -> None:
    resolution = resolve_preview_label(PartitionFilterConfig())

    assert resolution is not None
    assert resolution.owner is PartitionFilterConfig
    assert resolution.label == "FILT"


def test_plain_partition_filter_preview_requires_a_selection() -> None:
    assert format_partition_filter_config(PartitionFilterConfig(), "partition_filter") is None
    assert (
        format_partition_filter_config(
            PartitionFilterConfig(
                partition_filter=["A01", "A02"],
                partition_filter_mode=ExcludePartitions,
            ),
            "partition_filter",
        )
        == "FILT-2"
    )


def test_lazy_plain_partition_filter_preserves_base_preview_policy() -> None:
    resolution = resolve_preview_label(LazyPartitionFilterConfig())

    assert resolution is not None
    assert resolution.owner is PartitionFilterConfig
    assert format_partition_filter_config(LazyPartitionFilterConfig(), "partition_filter") is None


def test_lazy_specialized_config_uses_its_declared_preview_policy() -> None:
    config = LazyNapariStreamingConfig(enabled=True)
    resolution = resolve_preview_label(config)

    assert resolution is not None
    assert resolution.owner is NapariStreamingConfig
    assert format_partition_filter_config(config, "napari_streaming_config") == "NAP"


def test_specialized_preview_labels_are_derived_from_subclass_declarations() -> None:
    assert (
        format_partition_filter_config(
            NapariStreamingConfig(enabled=True),
            "napari_streaming_config",
        )
        == "NAP"
    )
    assert (
        format_partition_filter_config(
            StepMaterializationConfig(enabled=True),
            "step_materialization_config",
        )
        == "MAT"
    )
