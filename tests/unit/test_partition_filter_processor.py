from openhcs.core.config import PartitionFilterMode
from openhcs.core.partition_filter import PartitionFilterProcessor


def test_partition_filter_preserves_available_identity_across_case_variants() -> None:
    available = ["r04c09", "r04c10"]

    assert PartitionFilterProcessor.resolve_filter_with_mode(
        "R04C09",
        PartitionFilterMode.INCLUDE,
        available,
    ) == ["r04c09"]
    assert PartitionFilterProcessor.resolve_filter_with_mode(
        ["R04C10"],
        PartitionFilterMode.INCLUDE,
        available,
    ) == ["r04c10"]
    assert PartitionFilterProcessor.resolve_filter_with_mode(
        "R04C09",
        PartitionFilterMode.EXCLUDE,
        available,
    ) == ["r04c10"]
