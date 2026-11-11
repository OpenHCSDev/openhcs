from __future__ import annotations

from abc import ABC
from enum import Enum
from typing import ClassVar

from metaclass_registry import AutoRegisterMeta


class ObjectLabelRepresentation(str, Enum):
    """Storage representation used by an object-label artifact payload."""

    DENSE_LABELS = "dense_labels"
    SPARSE_IJV = "sparse_ijv"


class ObjectLabelVariant(ABC, metaclass=AutoRegisterMeta):
    """A named label array carried beside an object set's final labels.

    The kernel declares only the final labels; a domain declares further
    variants (for example labels before editing) as subclasses.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True

    name: ClassVar[str]
