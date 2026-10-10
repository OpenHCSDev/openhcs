"""
Generic validation system for component-agnostic validation.

This module provides a generic replacement for the component-specific validation
logic, supporting any component configuration and validation patterns.
"""

import logging
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Sequence

from openhcs.core.axes import Axis, AxisFamily, GroupingDeclaration

logger = logging.getLogger(__name__)


@dataclass
class ValidationResult:
    """Result of a validation operation."""

    is_valid: bool
    error_message: Optional[str] = None
    warnings: Optional[List[str]] = None


class GenericValidator:
    """Step validation over an axis family's declared constraints."""

    def __init__(self, family: type[AxisFamily]):
        self.family = family

    def validate_step(
        self,
        variable_components: Sequence[type[Axis]],
        group_by: type[GroupingDeclaration] | None,
        is_grouped: bool,
        step_name: str,
    ) -> ValidationResult:
        """Validate one step's variable axes and grouping against the family.

        Args:
            variable_components: Axes the step assembles along
            group_by: The step's grouping declaration
            is_grouped: Whether the admitted function pattern dispatches by group
            step_name: Name of the step for error reporting
        """
        grouping_axes = () if group_by is None else group_by.grouping_axes()
        overlap = [axis for axis in grouping_axes if axis in variable_components]
        if overlap:
            return ValidationResult(
                is_valid=False,
                error_message=(
                    f"group_by {overlap[0].name} cannot be in variable_components "
                    f"{[axis.name for axis in variable_components]}"
                ),
            )

        if is_grouped and not grouping_axes:
            return ValidationResult(
                is_valid=False,
                error_message=(
                    f"Dict pattern requires a concrete group_by axis in "
                    f"step '{step_name}'. variable_components declares the "
                    "3D stack axis; dict keys declare dispatch groups and "
                    "cannot use Ungrouped."
                ),
            )

        variable_axes = self.family.variable_axes()
        partition_name = self.family.partition_axis().name
        for axis in variable_components:
            if axis not in variable_axes:
                return ValidationResult(
                    is_valid=False,
                    error_message=(
                        f"Variable component {axis.name} not available "
                        f"(multiprocessing axis: {partition_name})"
                    ),
                )

        for axis in grouping_axes:
            if axis not in variable_axes:
                return ValidationResult(
                    is_valid=False,
                    error_message=(
                        f"Group_by component {axis.name} not available "
                        f"(multiprocessing axis: {partition_name})"
                    ),
                )

        return ValidationResult(is_valid=True)

    def validate_dict_pattern_keys(
        self,
        func_pattern: Dict[str, Any],
        group_by: type[Axis],
        step_name: str,
        orchestrator,
        *,
        resolved_config=None,
    ) -> ValidationResult:
        """
        Validate that dict function pattern keys match available component keys.

        This validation ensures compile-time guarantee that dict patterns will work
        at runtime by checking that all dict keys exist in the actual component data.

        Args:
            func_pattern: Dict function pattern to validate
            group_by: Axis whose values key the dict pattern
            step_name: Name of the step containing the function
            orchestrator: Orchestrator for component key access
            resolved_config: Held compilation configuration, or live saved configuration.

        Returns:
            ValidationResult indicating success or failure
        """
        from openhcs.core.function_patterns import NormalizedFunctionPattern

        try:
            # Use enum objects directly - orchestrator now accepts VariableComponents
            available_keys = orchestrator.get_component_keys(
                group_by, resolved_config=resolved_config
            )
            available_keys_set = set(str(key) for key in available_keys)

            # Check each dict key against available keys
            pattern_keys = (
                func_pattern.source_group_keys
                if isinstance(func_pattern, NormalizedFunctionPattern)
                else tuple(func_pattern)
            )
            pattern_keys_set = set(str(key) for key in pattern_keys)

            # Try direct string match first
            missing_keys = pattern_keys_set - available_keys_set

            if missing_keys:
                # Try numeric conversion for better error reporting
                try:
                    available_numeric = {
                        str(int(float(k)))
                        for k in available_keys
                        if str(k).replace(".", "").isdigit()
                    }
                    pattern_numeric = {
                        str(int(float(k)))
                        for k in pattern_keys
                        if str(k).replace(".", "").isdigit()
                    }
                    missing_numeric = pattern_numeric - available_numeric

                    if missing_numeric:
                        return ValidationResult(
                            is_valid=False,
                            error_message=(
                                f"Function pattern keys {sorted(missing_numeric)} not found in available "
                                f"{group_by.name} components {sorted(available_numeric)} for step '{step_name}'"
                            ),
                        )
                except (ValueError, TypeError):
                    # Fall back to string comparison
                    return ValidationResult(
                        is_valid=False,
                        error_message=(
                            f"Function pattern keys {sorted(missing_keys)} not found in available "
                            f"{group_by.name} components {sorted(available_keys_set)} for step '{step_name}'"
                        ),
                    )

            return ValidationResult(is_valid=True)

        except Exception as e:
            return ValidationResult(
                is_valid=False,
                error_message=f"Failed to validate dict pattern keys for {group_by.name}: {e}",
            )
