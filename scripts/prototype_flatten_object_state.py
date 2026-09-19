"""
Prototype for flattening ObjectState - dry run before actual refactor.

Tests core concepts:
1. _extract_all_parameters_flat() - dotted path generation
2. _path_to_type mapping
3. to_object() reconstruction
4. Type-based invalidation
"""

import dataclasses
from dataclasses import dataclass, fields, is_dataclass
from typing import Any, Dict, Optional, Set
import logging

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


# ========== Test Dataclasses ==========


@dataclass
class WellFilterConfig:
    """Base well filter config."""

    well_filter: Optional[int] = None
    enabled: bool = True


@dataclass
class StepWellFilterConfig(WellFilterConfig):
    """Step-level well filter config (inherits from base)."""

    step_specific_param: Optional[str] = None


@dataclass
class NapariStreamingConfig:
    """Napari streaming config."""

    window_size: int = 10
    buffer_size: int = 100


@dataclass
class GlobalPipelineConfig:
    """Test global config with nested dataclasses."""

    well_filter_config: Optional[WellFilterConfig] = None
    napari_streaming_config: Optional[NapariStreamingConfig] = None
    some_top_level_param: str = "default"


@dataclass
class FunctionStep:
    """Function step with nested config."""

    name: str = "step"
    step_well_filter_config: Optional[StepWellFilterConfig] = None
    processing_config: Optional[Any] = None


# ========== Prototype Flat ObjectState ==========


class FlatObjectState:
    """Prototype of flat ObjectState with dotted paths."""

    def __init__(self, object_instance: Any):
        self.object_instance = object_instance
        self.parameters: Dict[str, Any] = {}
        self._path_to_type: Dict[str, type] = {}
        self._invalid_fields: Set[str] = set()
        self._cached_object: Optional[Any] = None

        # Extract all parameters flat
        self._extract_all_parameters_flat(object_instance, prefix="")

    def _extract_all_parameters_flat(self, obj: Any, prefix: str) -> None:
        """Recursively extract parameters into flat dict with dotted paths.

        Args:
            obj: Object to extract from
            prefix: Current path prefix (e.g., 'well_filter_config')
        """
        if not is_dataclass(obj):
            return

        obj_type = type(obj)

        for field in fields(obj):
            field_name = field.name
            field_type = field.type

            # Build dotted path
            dotted_path = f"{prefix}.{field_name}" if prefix else field_name

            # Get current value (bypassing lazy resolution)
            try:
                current_value = object.__getattribute__(obj, field_name)
            except AttributeError:
                current_value = None

            # Check if this is a nested dataclass
            nested_type = self._get_nested_dataclass_type(field_type)

            if nested_type is not None and current_value is not None:
                # Store the reference to nested config type at this prefix
                # This is important for knowing what type to instantiate during to_object()
                self._path_to_type[dotted_path] = nested_type

                # Recurse into nested dataclass
                self._extract_all_parameters_flat(current_value, prefix=dotted_path)
            else:
                # Leaf field - store value and container type
                self.parameters[dotted_path] = current_value
                # Store the CONTAINER type (the type that has this field)
                self._path_to_type[dotted_path] = obj_type

                logger.info(
                    f"  Extracted: {dotted_path} = {current_value} (container={obj_type.__name__})"
                )

    def _get_nested_dataclass_type(self, field_type: Any) -> Optional[type]:
        """Check if field_type is a dataclass (handles Optional[T])."""
        # Handle Optional[T]
        if hasattr(field_type, "__origin__"):
            from typing import Union

            if field_type.__origin__ is Union:
                # Get non-None types
                non_none_types = [
                    arg for arg in field_type.__args__ if arg is not type(None)
                ]
                if len(non_none_types) == 1:
                    field_type = non_none_types[0]

        # Check if it's a dataclass type
        if is_dataclass(field_type):
            return field_type

        return None

    def to_object(self) -> Any:
        """Reconstruct full nested dataclass from flat parameters.

        BOUNDARY METHOD - only call at save/execute/serialize boundaries.
        """
        if self._cached_object is not None:
            logger.info("✓ Using cached object")
            return self._cached_object

        logger.info("Reconstructing object from flat parameters...")
        self._cached_object = self._reconstruct_from_prefix("")
        return self._cached_object

    def _reconstruct_from_prefix(self, prefix: str) -> Any:
        """Recursively reconstruct dataclass from flat parameters.

        Args:
            prefix: Current path prefix (e.g., 'well_filter_config')

        Returns:
            Reconstructed dataclass instance
        """
        # Determine the type to reconstruct
        if not prefix:
            # Root level - use object_instance type
            obj_type = type(self.object_instance)
        else:
            # Nested level - look up type from _path_to_type
            obj_type = self._path_to_type.get(prefix)
            if obj_type is None:
                raise ValueError(f"No type mapping for prefix: {prefix}")

        prefix_dot = f"{prefix}." if prefix else ""

        # Collect direct fields and nested prefixes
        direct_fields = {}
        nested_prefixes = set()

        for path, value in self.parameters.items():
            if not path.startswith(prefix_dot):
                continue

            remainder = path[len(prefix_dot) :]

            if "." in remainder:
                # This is a nested field - collect the first component
                first_component = remainder.split(".")[0]
                nested_prefixes.add(first_component)
            else:
                # Direct field of this object
                direct_fields[remainder] = value

        # Reconstruct nested dataclasses first
        for nested_name in nested_prefixes:
            nested_path = f"{prefix_dot}{nested_name}"
            nested_obj = self._reconstruct_from_prefix(nested_path)
            direct_fields[nested_name] = nested_obj

        # Filter out None values for lazy resolution
        filtered_fields = {k: v for k, v in direct_fields.items() if v is not None}

        # Instantiate the dataclass
        logger.info(
            f"  Reconstructing {obj_type.__name__} with fields: {list(filtered_fields.keys())}"
        )
        return obj_type(**filtered_fields)

    def update_parameter(self, dotted_path: str, value: Any) -> None:
        """Update a parameter value.

        Args:
            dotted_path: Full dotted path (e.g., 'well_filter_config.well_filter')
            value: New value
        """
        if dotted_path not in self.parameters:
            logger.warning(f"Path not found: {dotted_path}")
            return

        self.parameters[dotted_path] = value
        self._invalid_fields.add(dotted_path)
        self._cached_object = None  # Invalidate cache
        logger.info(f"Updated: {dotted_path} = {value}")

    def invalidate_by_type_and_field(self, target_type: type, field_name: str) -> None:
        """Invalidate all fields matching target_type and field_name.

        This simulates the type-based invalidation from ObjectStateRegistry.
        """
        logger.info(f"Invalidating {target_type.__name__}.{field_name}...")

        for path, path_type in self._path_to_type.items():
            # Check if target_type is in the MRO of path_type
            if target_type in path_type.__mro__:
                # Check if path ends with the field_name
                if path.endswith(f".{field_name}") or path == field_name:
                    self._invalid_fields.add(path)
                    logger.info(
                        f"  ✓ Invalidated: {path} (container={path_type.__name__})"
                    )

        self._cached_object = None


# ========== Tests ==========


def test_extraction():
    """Test 1: Parameter extraction with dotted paths."""
    print("\n" + "=" * 80)
    print("TEST 1: Parameter Extraction with Dotted Paths")
    print("=" * 80)

    # Create a test instance with nested configs
    config = GlobalPipelineConfig(
        well_filter_config=WellFilterConfig(well_filter=2, enabled=True),
        napari_streaming_config=NapariStreamingConfig(window_size=20),
        some_top_level_param="custom",
    )

    state = FlatObjectState(config)

    print("\nExtracted parameters:")
    for path, value in sorted(state.parameters.items()):
        container_type = state._path_to_type.get(path)
        print(
            f"  {path:50s} = {str(value):20s} (container={container_type.__name__ if container_type else 'N/A'})"
        )

    print("\nPath-to-type mapping:")
    for path, typ in sorted(state._path_to_type.items()):
        print(f"  {path:50s} → {typ.__name__}")

    # Validate expected paths exist
    expected_paths = [
        "well_filter_config.well_filter",
        "well_filter_config.enabled",
        "napari_streaming_config.window_size",
        "napari_streaming_config.buffer_size",
        "some_top_level_param",
    ]

    for path in expected_paths:
        assert path in state.parameters, f"Missing expected path: {path}"

    print("\n✓ All expected paths found!")


def test_reconstruction():
    """Test 2: Object reconstruction from flat parameters."""
    print("\n" + "=" * 80)
    print("TEST 2: Object Reconstruction from Flat Parameters")
    print("=" * 80)

    # Create original
    original = GlobalPipelineConfig(
        well_filter_config=WellFilterConfig(well_filter=2, enabled=True),
        napari_streaming_config=NapariStreamingConfig(window_size=20),
        some_top_level_param="custom",
    )

    # Flatten
    state = FlatObjectState(original)

    # Reconstruct
    reconstructed = state.to_object()

    print("\nOriginal:")
    print(f"  {original}")
    print("\nReconstructed:")
    print(f"  {reconstructed}")

    # Verify equality
    assert reconstructed.some_top_level_param == original.some_top_level_param
    assert (
        reconstructed.well_filter_config.well_filter
        == original.well_filter_config.well_filter
    )
    assert (
        reconstructed.well_filter_config.enabled == original.well_filter_config.enabled
    )
    assert (
        reconstructed.napari_streaming_config.window_size
        == original.napari_streaming_config.window_size
    )

    print("\n✓ Reconstruction successful - all fields match!")


def test_update_and_invalidation():
    """Test 3: Update parameter and check invalidation."""
    print("\n" + "=" * 80)
    print("TEST 3: Update Parameter and Cache Invalidation")
    print("=" * 80)

    config = GlobalPipelineConfig(
        well_filter_config=WellFilterConfig(well_filter=2),
    )

    state = FlatObjectState(config)

    # First reconstruction - should compute
    obj1 = state.to_object()
    print(f"\nFirst call: {obj1.well_filter_config.well_filter}")

    # Second call - should use cache
    obj2 = state.to_object()
    print(f"Second call (cached): {obj2.well_filter_config.well_filter}")
    assert obj1 is obj2, "Should return same cached object"

    # Update parameter - should invalidate cache
    state.update_parameter("well_filter_config.well_filter", 5)

    # Third call - should recompute
    obj3 = state.to_object()
    print(f"After update: {obj3.well_filter_config.well_filter}")
    assert obj3.well_filter_config.well_filter == 5
    assert obj3 is not obj1, "Should create new object after cache invalidation"

    print("\n✓ Cache invalidation working correctly!")


def test_type_based_invalidation():
    """Test 4: Type-based invalidation with MRO."""
    print("\n" + "=" * 80)
    print("TEST 4: Type-Based Invalidation (Sibling Inheritance)")
    print("=" * 80)

    # Create a FunctionStep with StepWellFilterConfig
    step = FunctionStep(
        name="my_step",
        step_well_filter_config=StepWellFilterConfig(
            well_filter=3, enabled=False, step_specific_param="test"
        ),
    )

    state = FlatObjectState(step)

    print("\nExtracted paths:")
    for path in sorted(state.parameters.keys()):
        print(f"  {path}")

    # Simulate: WellFilterConfig.well_filter changed in another scope
    # Should invalidate StepWellFilterConfig.well_filter (sibling inheritance)
    print("\nInvalidating WellFilterConfig.well_filter...")
    state.invalidate_by_type_and_field(WellFilterConfig, "well_filter")

    print(f"\nInvalid fields: {state._invalid_fields}")

    # Should have invalidated step_well_filter_config.well_filter
    expected_invalid = "step_well_filter_config.well_filter"
    assert (
        expected_invalid in state._invalid_fields
    ), f"Should invalidate {expected_invalid}"

    print(f"\n✓ Type-based invalidation working - {expected_invalid} was invalidated!")


def test_field_prefix_pattern():
    """Test 5: PFM field_prefix pattern."""
    print("\n" + "=" * 80)
    print("TEST 5: PFM Field Prefix Pattern")
    print("=" * 80)

    config = GlobalPipelineConfig(
        well_filter_config=WellFilterConfig(well_filter=2, enabled=True),
    )

    state = FlatObjectState(config)

    # Simulate root PFM (field_prefix = '')
    root_prefix = ""

    # Simulate nested PFM (field_prefix = 'well_filter_config')
    nested_prefix = "well_filter_config"

    # Root PFM accesses top-level params
    def get_field_value(prefix: str, field_name: str):
        dotted_path = f"{prefix}.{field_name}" if prefix else field_name
        return state.parameters.get(dotted_path)

    # Test root access
    top_level_value = get_field_value(root_prefix, "some_top_level_param")
    print(f"Root PFM accessing 'some_top_level_param': {top_level_value}")

    # Test nested access
    well_filter_value = get_field_value(nested_prefix, "well_filter")
    enabled_value = get_field_value(nested_prefix, "enabled")
    print(f"Nested PFM accessing 'well_filter': {well_filter_value}")
    print(f"Nested PFM accessing 'enabled': {enabled_value}")

    assert well_filter_value == 2
    assert enabled_value == True

    print("\n✓ Field prefix pattern works correctly!")


def test_none_handling():
    """Test 6: None value handling (lazy resolution)."""
    print("\n" + "=" * 80)
    print("TEST 6: None Value Handling (Lazy Resolution)")
    print("=" * 80)

    # Create config with some None values (lazy)
    config = GlobalPipelineConfig(
        well_filter_config=WellFilterConfig(
            well_filter=None, enabled=True  # Lazy - should inherit
        ),
        some_top_level_param="custom",
    )

    state = FlatObjectState(config)

    print("\nFlat parameters (including None):")
    for path, value in sorted(state.parameters.items()):
        print(f"  {path:50s} = {value}")

    # Reconstruct - None values should be filtered during instantiation
    reconstructed = state.to_object()

    print("\nReconstructed object:")
    print(
        f"  well_filter_config.well_filter: {reconstructed.well_filter_config.well_filter}"
    )
    print(f"  well_filter_config.enabled: {reconstructed.well_filter_config.enabled}")

    # The reconstructed object should have None for well_filter (not set in filtered_fields)
    assert reconstructed.well_filter_config.well_filter is None
    assert reconstructed.well_filter_config.enabled is True

    print("\n✓ None handling correct - lazy fields preserved!")


# ========== Main ==========

if __name__ == "__main__":
    print("\n" + "=" * 80)
    print("FLAT OBJECTSTATE PROTOTYPE - DRY RUN")
    print("=" * 80)

    try:
        test_extraction()
        test_reconstruction()
        test_update_and_invalidation()
        test_type_based_invalidation()
        test_field_prefix_pattern()
        test_none_handling()

        print("\n" + "=" * 80)
        print("✓ ALL TESTS PASSED - FLAT OBJECTSTATE DESIGN IS SOUND!")
        print("=" * 80)

    except AssertionError as e:
        print(f"\n✗ TEST FAILED: {e}")
        raise
    except Exception as e:
        print(f"\n✗ ERROR: {e}")
        raise
