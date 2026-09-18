"""
OpenHCS pipeline migration utilities (optional integration)

This module provides utilities to migrate old OpenHCS pipeline files that contain
legacy enum values to the new variable component system.

The migration handles:
- Converting old string-based GroupBy enum values to new VariableComponents-based values
- Preserving all other step attributes and functionality
- Creating atomic backups during migration
- Detecting legacy pipeline format automatically

Usage:
    from openhcs.utils.pipeline_migration import migrate_pipeline_file, detect_legacy_pipeline

    # Check if migration is needed
    if detect_legacy_pipeline(steps):
        success = migrate_pipeline_file(pipeline_path)
"""

import logging
from pathlib import Path
from typing import Any, List, Dict, Optional
from contextlib import contextmanager
import dill as pickle

logger = logging.getLogger(__name__)


def detect_legacy_pipeline(steps: List[Any]) -> bool:
    """
    Detect if pipeline contains legacy format with direct attributes on step.

    OLD format: step.group_by and step.variable_components as direct attributes
    NEW format: step.processing_config.group_by and step.processing_config.variable_components

    Args:
        steps: List of pipeline steps

    Returns:
        True if legacy format detected, False otherwise
    """
    try:
        for step in steps:
            # Check if step has direct group_by attribute (OLD format)
            if hasattr(step, "group_by") and not hasattr(step, "processing_config"):
                logger.debug(f"Legacy direct group_by attribute detected on step")
                return True

            # Check if step has direct variable_components attribute (OLD format)
            if hasattr(step, "variable_components") and not hasattr(
                step, "processing_config"
            ):
                logger.debug(
                    f"Legacy direct variable_components attribute detected on step"
                )
                return True

            # Also check for string-based enum values in processing_config (secondary migration)
            if hasattr(step, "processing_config"):
                if hasattr(step.processing_config, "group_by") and isinstance(
                    step.processing_config.group_by, str
                ):
                    logger.debug(
                        f"Legacy string group_by detected in processing_config: {step.processing_config.group_by}"
                    )
                    return True

                if (
                    hasattr(step.processing_config, "variable_components")
                    and step.processing_config.variable_components
                ):
                    for component in step.processing_config.variable_components:
                        if isinstance(component, str):
                            logger.debug(
                                f"Legacy string variable_component detected in processing_config: {component}"
                            )
                            return True

        return False
    except Exception as e:
        logger.warning(f"Error detecting legacy pipeline format: {e}")
        return False


def create_migration_mapping(enum_class) -> Dict[str, Any]:
    """
    Create migration mapping from enum using clean functional approach.
    Single source of truth for all migration mappings.
    """
    # Special cases for NONE enum
    mapping = (
        {"": enum_class.NONE, "none": enum_class.NONE}
        if hasattr(enum_class, "NONE")
        else {}
    )

    # Generate all variations using dict comprehension - Pythonic and clean
    variations = {
        variation: member
        for member in enum_class
        if member.value is not None
        for variation in _generate_string_variations(member)
    }

    return {**mapping, **variations}


def _generate_string_variations(enum_member):
    """Generate string variations for enum member - clean and functional."""
    base_strings = [enum_member.name, enum_member.value]
    return [
        variant.lower()
        for base in base_strings
        for variant in [base, base.replace("_", "")]
    ]


def migrate_legacy_group_by(group_by_value: Any) -> Any:
    """Clean migration using single mapping source."""
    if not isinstance(group_by_value, str):
        return group_by_value

    from openhcs.constants.constants import GroupBy

    migration_map = create_migration_mapping(GroupBy)
    migrated_value = migration_map.get(group_by_value.lower())

    if migrated_value:
        logger.debug(f"Migrated group_by: '{group_by_value}' -> {migrated_value}")
        return migrated_value

    logger.warning(f"Legacy group_by '{group_by_value}' not available - using NONE")
    return GroupBy.NONE


def migrate_legacy_variable_components(variable_components: List[Any]) -> List[Any]:
    """Clean migration for variable components using functional approach."""
    if not variable_components:
        return variable_components

    from openhcs.constants.constants import VariableComponents

    migration_map = create_migration_mapping(VariableComponents)

    # Functional approach using list comprehension
    migrated = []
    for comp in variable_components:
        if isinstance(comp, str):
            migrated_comp = migration_map.get(comp.lower())
            if migrated_comp:
                logger.debug(
                    f"Migrated variable_component: '{comp}' -> {migrated_comp}"
                )
                migrated.append(migrated_comp)
            else:
                logger.warning(
                    f"Legacy variable_component '{comp}' not available - skipping"
                )
        else:
            # Already an enum - keep as-is
            migrated.append(comp)

    return migrated


def migrate_pipeline_steps(steps: List[Any]) -> List[Any]:
    """
    Migrate pipeline steps from legacy format to new LazyProcessingConfig structure.

    OLD format: step.group_by and step.variable_components as direct attributes
    NEW format: step.processing_config.group_by and step.processing_config.variable_components

    Args:
        steps: List of pipeline steps to migrate

    Returns:
        List of migrated pipeline steps
    """
    from openhcs.core.config import LazyProcessingConfig

    migrated_steps = []

    for step in steps:
        # Handle OLD format: direct attributes on step
        if hasattr(step, "group_by") or hasattr(step, "variable_components"):
            # Ensure step has processing_config
            if not hasattr(step, "processing_config"):
                step.processing_config = LazyProcessingConfig()

            # Migrate group_by from direct attribute to processing_config
            if hasattr(step, "group_by"):
                old_group_by = getattr(step, "group_by")
                migrated_group_by = migrate_legacy_group_by(old_group_by)
                # Set in processing_config (need to handle frozen dataclass)
                object.__setattr__(
                    step.processing_config, "group_by", migrated_group_by
                )
                # Remove old direct attribute
                delattr(step, "group_by")
                logger.debug(
                    f"Migrated group_by from direct attribute to processing_config"
                )

            # Migrate variable_components from direct attribute to processing_config
            if hasattr(step, "variable_components"):
                old_variable_components = getattr(step, "variable_components")
                migrated_variable_components = migrate_legacy_variable_components(
                    old_variable_components
                )
                # Set in processing_config (need to handle frozen dataclass)
                object.__setattr__(
                    step.processing_config,
                    "variable_components",
                    migrated_variable_components,
                )
                # Remove old direct attribute
                delattr(step, "variable_components")
                logger.debug(
                    f"Migrated variable_components from direct attribute to processing_config"
                )

        # Handle secondary migration: string-based enums in processing_config
        if hasattr(step, "processing_config"):
            # Migrate string-based group_by in processing_config
            if hasattr(step.processing_config, "group_by") and isinstance(
                step.processing_config.group_by, str
            ):
                migrated_group_by = migrate_legacy_group_by(
                    step.processing_config.group_by
                )
                object.__setattr__(
                    step.processing_config, "group_by", migrated_group_by
                )
                logger.debug(f"Migrated string group_by in processing_config to enum")

            # Migrate string-based variable_components in processing_config
            if (
                hasattr(step.processing_config, "variable_components")
                and step.processing_config.variable_components
            ):
                if any(
                    isinstance(comp, str)
                    for comp in step.processing_config.variable_components
                ):
                    migrated_variable_components = migrate_legacy_variable_components(
                        step.processing_config.variable_components
                    )
                    object.__setattr__(
                        step.processing_config,
                        "variable_components",
                        migrated_variable_components,
                    )
                    logger.debug(
                        f"Migrated string variable_components in processing_config to enums"
                    )

        migrated_steps.append(step)

    return migrated_steps


def migrate_pipeline_file(pipeline_path: Path, backup_suffix: str = ".backup") -> bool:
    """
    Migrate a pipeline file from legacy format to new enum structure.

    Args:
        pipeline_path: Path to pipeline file
        backup_suffix: Suffix for backup file

    Returns:
        True if migration was needed and successful, False otherwise
    """
    if not pipeline_path.exists():
        logger.error(f"Pipeline file not found: {pipeline_path}")
        return False

    # Load existing pipeline
    try:
        with open(pipeline_path, "rb") as f:
            steps = pickle.load(f)
    except Exception as e:
        logger.error(f"Failed to load pipeline from {pipeline_path}: {e}")
        return False

    if not isinstance(steps, list):
        logger.error(
            f"Invalid pipeline format in {pipeline_path}: expected list, got {type(steps)}"
        )
        return False

    # Check if migration is needed
    if not detect_legacy_pipeline(steps):
        logger.info(
            f"Pipeline file {pipeline_path} is already in new format - no migration needed"
        )
        return False

    logger.info(f"Legacy format detected in {pipeline_path}")

    # Perform migration
    try:
        migrated_steps = migrate_pipeline_steps(steps)
    except Exception as e:
        logger.error(f"Failed to migrate pipeline: {e}")
        return False

    # Create backup
    backup_file = pipeline_path.with_suffix(f"{pipeline_path.suffix}{backup_suffix}")
    try:
        pipeline_path.rename(backup_file)
        logger.info(f"Created backup: {backup_file}")
    except OSError as e:
        logger.error(f"Failed to create backup: {e}")
        return False

    # Write migrated pipeline
    try:
        with open(pipeline_path, "wb") as f:
            pickle.dump(migrated_steps, f)
        logger.info(f"Successfully migrated pipeline file: {pipeline_path}")
        return True
    except Exception as e:
        logger.error(f"Failed to write migrated pipeline: {e}")
        # Restore backup
        try:
            backup_file.rename(pipeline_path)
            logger.info("Restored original file from backup")
        except OSError:
            logger.error(
                f"Failed to restore backup - original file is at {backup_file}"
            )
        return False


class LegacyGroupByUnpickler(pickle.Unpickler):
    """
    Custom unpickler that handles legacy GroupBy enum values during deserialization.

    This unpickler intercepts the creation of GroupBy enum instances and converts
    legacy string values to the new VariableComponents-based structure.
    """

    def find_class(self, module, name):
        """Override find_class to handle GroupBy enum migration."""
        # Get the original class
        cls = super().find_class(module, name)

        # If this is the GroupBy enum, wrap it with migration logic
        if name == "GroupBy" and module == "openhcs.constants.constants":
            return self._create_migrating_groupby_class(cls)

        return cls

    def _create_migrating_groupby_class(self, original_groupby_class):
        """Clean unpickler using single migration mapping source."""

        class MigratingGroupBy:
            """Wrapper that migrates legacy string values using clean mapping."""

            def __new__(cls, value):
                # If it's already a GroupBy enum, return it as-is
                if (
                    hasattr(value, "__class__")
                    and value.__class__.__name__ == "GroupBy"
                ):
                    return value

                # Handle legacy string values
                if isinstance(value, str):
                    from openhcs.constants.constants import GroupBy

                    # Use same clean migration mapping
                    migration_map = create_migration_mapping(GroupBy)
                    migrated_value = migration_map.get(value.lower())

                    if migrated_value:
                        logger.debug(
                            f"Unpickler migrated: '{value}' -> {migrated_value}"
                        )
                        return migrated_value

                    logger.warning(f"Unpickler: '{value}' not available - using NONE")
                    return GroupBy.NONE

                # Fallback for other types
                try:
                    return original_groupby_class(value)
                except ValueError:
                    logger.warning(f"Failed to create GroupBy from value: {value}")
                    from openhcs.constants.constants import GroupBy

                    return GroupBy.NONE

        return MigratingGroupBy


def load_pipeline_with_migration(pipeline_path: Path) -> Optional[List[Any]]:
    """
    Load pipeline file with automatic migration if needed.

    This is the main function that should be used by the PyQt GUI
    to load pipeline files with backward compatibility.

    Args:
        pipeline_path: Path to pipeline file

    Returns:
        List of pipeline steps or None if loading failed
    """
    try:
        # Load pipeline using custom unpickler for enum migration
        with open(pipeline_path, "rb") as f:
            unpickler = LegacyGroupByUnpickler(f)
            steps = unpickler.load()

        if not isinstance(steps, list):
            logger.error(f"Invalid pipeline format: expected list, got {type(steps)}")
            return None

        # Check if migration is needed
        if detect_legacy_pipeline(steps):
            logger.info(f"Migrating legacy pipeline format in {pipeline_path}")

            # Migrate in-memory (don't modify the file unless explicitly requested)
            migrated_steps = migrate_pipeline_steps(steps)

            # Optionally save the migrated version back to file
            # For now, just return the migrated steps without saving
            logger.info(
                "Pipeline migrated in-memory. Use migrate_pipeline_file() to save changes."
            )
            return migrated_steps

        return steps

    except Exception as e:
        logger.error(f"Failed to load pipeline from {pipeline_path}: {e}")
        return None


@contextmanager
def patch_step_constructors_for_migration():
    """
    Context manager that patches AbstractStep constructors to accept old-format parameters.

    OLD format: step = SomeStep(name="test", group_by=GroupBy.WELL, variable_components=[...])
    NEW format: step = SomeStep(name="test", processing_config=LazyProcessingConfig(group_by=GroupBy.WELL, ...))

    This allows Python source code with old-style step constructors to work without modification.
    Only applied when TypeError is detected, so no overhead for new-format code.

    Usage:
        try:
            exec(code, namespace)
        except TypeError as e:
            if "unexpected keyword argument" in str(e) and "group_by" in str(e):
                with patch_step_constructors_for_migration():
                    exec(code, namespace)
    """
    from openhcs.core.steps.abstract import AbstractStep
    from openhcs.core.config import LazyProcessingConfig
    from dataclasses import replace

    # Save original __init__
    original_init = AbstractStep.__init__

    def migrating_init(self, **kwargs):
        """Wrapper that migrates old-format parameters to new processing_config structure."""
        # Extract old-format parameters if present
        old_group_by = kwargs.pop("group_by", None)
        old_variable_components = kwargs.pop("variable_components", None)

        # If old-format parameters exist, merge them into processing_config
        if old_group_by is not None or old_variable_components is not None:
            logger.debug(
                f"Migrating old-format constructor parameters for {self.__class__.__name__}"
            )

            # Get existing processing_config or create new one
            existing_config = kwargs.get("processing_config", LazyProcessingConfig())

            # Build new config with migrated values
            config_kwargs = {}
            if old_group_by is not None:
                config_kwargs["group_by"] = old_group_by
                logger.debug(f"  - Migrated group_by: {old_group_by}")
            if old_variable_components is not None:
                config_kwargs["variable_components"] = old_variable_components
                logger.debug(
                    f"  - Migrated variable_components: {old_variable_components}"
                )

            # Merge with existing config using dataclass replace
            if config_kwargs:
                kwargs["processing_config"] = replace(existing_config, **config_kwargs)

        # Call original __init__ with migrated kwargs
        original_init(self, **kwargs)

    # Apply patch
    AbstractStep.__init__ = migrating_init

    try:
        yield
    finally:
        # Restore original __init__
        AbstractStep.__init__ = original_init
