"""
Test flat ObjectState prototype with REAL GlobalPipelineConfig.

This validates that the approach works with the actual complex nested structure.
"""

import sys

sys.path.insert(0, "/home/ts/code/projects/openhcs-sequential")

from openhcs.core.config import GlobalPipelineConfig
from scripts.prototype_flatten_object_state import FlatObjectState
import logging

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


def test_real_global_config():
    """Test with real GlobalPipelineConfig from codebase."""
    print("\n" + "=" * 80)
    print("TESTING WITH REAL GlobalPipelineConfig")
    print("=" * 80)

    # Create a real instance
    config = GlobalPipelineConfig()

    print(f"\nOriginal config type: {type(config)}")
    print(f"Original config: {config}")

    # Flatten it
    state = FlatObjectState(config)

    print(f"\n{'='*80}")
    print(f"FLATTENED STRUCTURE")
    print(f"{'='*80}")

    print(f"\nTotal parameters: {len(state.parameters)}")
    print(f"Total type mappings: {len(state._path_to_type)}")

    print("\nSample dotted paths (first 20):")
    for i, (path, value) in enumerate(sorted(state.parameters.items())):
        if i >= 20:
            print(f"  ... and {len(state.parameters) - 20} more")
            break
        container_type = state._path_to_type.get(path)
        value_str = str(value)[:30] if value is not None else "None"
        print(
            f"  {path:60s} = {value_str:30s} (container={container_type.__name__ if container_type else 'N/A'})"
        )

    # Find nested configs
    nested_configs = {path for path in state._path_to_type.keys() if "." not in path}
    print(f"\nNested configs found ({len(nested_configs)}):")
    for config_name in sorted(nested_configs):
        config_type = state._path_to_type.get(config_name)
        # Count fields in this nested config
        field_count = sum(
            1 for p in state.parameters.keys() if p.startswith(f"{config_name}.")
        )
        print(
            f"  {config_name:40s} ({config_type.__name__:30s}) - {field_count} fields"
        )

    # Reconstruct
    print(f"\n{'='*80}")
    print(f"RECONSTRUCTION TEST")
    print(f"{'='*80}")

    reconstructed = state.to_object()

    print(f"\nReconstructed type: {type(reconstructed)}")
    print(f"Reconstructed successfully: {type(reconstructed) == type(config)}")

    # Verify a few nested configs are correct
    if hasattr(config, "well_filter_config") and config.well_filter_config is not None:
        assert type(reconstructed.well_filter_config) == type(config.well_filter_config)
        print(f"✓ well_filter_config type matches")

    if (
        hasattr(config, "napari_streaming_config")
        and config.napari_streaming_config is not None
    ):
        assert type(reconstructed.napari_streaming_config) == type(
            config.napari_streaming_config
        )
        print(f"✓ napari_streaming_config type matches")

    # Test update and cache invalidation
    print(f"\n{'='*80}")
    print(f"UPDATE AND CACHE TEST")
    print(f"{'='*80}")

    # Find a field to update
    test_path = None
    for path in state.parameters.keys():
        if "well_filter" in path and path.endswith("well_filter"):
            test_path = path
            break

    if test_path:
        original_value = state.parameters[test_path]
        print(f"\nUpdating {test_path}: {original_value} → 999")

        state.update_parameter(test_path, 999)

        # Reconstruct again
        updated_obj = state.to_object()

        # Navigate to the field
        path_parts = test_path.split(".")
        current = updated_obj
        for part in path_parts[:-1]:
            current = getattr(current, part)
        final_value = getattr(current, path_parts[-1])

        print(f"Value after reconstruction: {final_value}")
        assert final_value == 999, f"Expected 999, got {final_value}"
        print(f"✓ Update propagated correctly")

    print(f"\n{'='*80}")
    print("✓ REAL GlobalPipelineConfig TEST PASSED!")
    print(f"{'='*80}")


if __name__ == "__main__":
    try:
        test_real_global_config()
    except Exception as e:
        print(f"\n✗ ERROR: {e}")
        import traceback

        traceback.print_exc()
        sys.exit(1)
