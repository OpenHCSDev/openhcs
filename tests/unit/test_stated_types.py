"""`Any` is refused where a user-facing declaration is consumed."""

from __future__ import annotations

import typing
from dataclasses import dataclass, field
from typing import Annotated, Any, Callable, Literal, Optional

import numpy as np
import pytest

from openhcs.core.memory.decorators import numpy as numpy_function
from openhcs.core.stated_types import (
    UnstatedTypeError,
    require_stated_field_types,
    require_stated_parameter_types,
    says_any,
)


@pytest.mark.parametrize("annotation", [
    Any,
    Optional[Any],
    dict[str, Any],
    Callable[..., Any],
    Callable[[Any], int],
    tuple[int, list[Any]],
    Annotated[Any, "described"],
    "Any",
    "dict[str, typing.Any] | None",
])
def test_any_is_found_at_any_depth(annotation: object) -> None:
    assert says_any(annotation, {"Any": Any, "typing": typing})


@pytest.mark.parametrize("annotation", [
    int,
    float | None,
    Literal["Any"],
    Annotated[int, Any],
    np.ndarray,
    "OnlyKnownToTheTypeChecker | None",
    "Literal['Any']",
])
def test_a_stated_type_is_not_any(annotation: object) -> None:
    assert not says_any(annotation, {"Any": Any, "typing": typing, "Literal": Literal})


@dataclass(frozen=True)
class Nested:
    stated: float = 0.0
    unstated: dict[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class Root:
    name: str = ""
    nested: Nested | None = None


def test_a_config_field_typed_any_is_refused_by_name_through_nesting() -> None:
    with pytest.raises(UnstatedTypeError, match=r"Root declares Nested\.unstated as Any"):
        require_stated_field_types(Root)


def test_every_config_root_states_its_field_types() -> None:
    """The roots call the check when they are declared; importing them is the proof."""
    from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
    from openhcs.pyqt_gui.config import UIConfig

    for root in (GlobalPipelineConfig, PipelineConfig, UIConfig):
        require_stated_field_types(root)


@numpy_function
def blur(image: np.ndarray, sigma: Any = 1.0, mode: Optional[Any] = None) -> np.ndarray:
    return image


@numpy_function
def stated_blur(image: np.ndarray, sigma: float = 1.0) -> np.ndarray:
    return image


def test_a_custom_function_parameter_typed_any_tells_the_user_to_state_it() -> None:
    from openhcs.processing.custom_functions.validation import validate_function

    refused = validate_function(blur)
    assert not refused.is_valid
    (message,) = refused.errors
    assert "'sigma', 'mode' as Any" in message
    assert "State each parameter's type" in message
    assert validate_function(stated_blur).is_valid


def test_catalogue_discovery_refuses_a_parameter_typed_any() -> None:
    from openhcs.processing.backends.lib_registry.openhcs_registry import OpenHCSRegistry

    registry = OpenHCSRegistry()
    with pytest.raises(UnstatedTypeError, match="'blur' declares 'sigma', 'mode' as Any"):
        registry._metadata_for_function("blur", blur, __name__)
    require_stated_parameter_types(stated_blur)
