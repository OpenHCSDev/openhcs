"""Domain sections of the global pipeline config.

A domain declares a config section as a dataclass inheriting
:class:`GlobalConfigSection`, in a module its axis family lists in
``config_modules``. The kernel config module imports those modules and adds
every declared section as a ``GlobalPipelineConfig`` field before its fields
are injected. Section modules import nothing from the kernel config, so they
may be imported in any order.
"""

from __future__ import annotations

from typing import ClassVar


class GlobalConfigSection:
    """A dataclass that becomes a field of the global pipeline config."""

    _declared: ClassVar[list[type["GlobalConfigSection"]]] = []

    def __init_subclass__(cls, **kwargs: object) -> None:
        super().__init_subclass__(**kwargs)
        GlobalConfigSection._declared.append(cls)

    @staticmethod
    def declared_sections() -> tuple[type["GlobalConfigSection"], ...]:
        return tuple(GlobalConfigSection._declared)


__all__ = ["GlobalConfigSection"]
