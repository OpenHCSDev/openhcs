"""Cross-package authority proofs for the memory-type taxonomy."""

import pickle

from openhcs.constants import MemoryType
from openhcs.constants.constants import MemoryType as RawConstantsMemoryType
from openhcs.core.memory import MemoryType as RuntimeMemoryType
from openhcs.constants.constants import MemoryType as PipelineMemoryType

from arraybridge import MemoryType as ArrayBridgeMemoryType


def test_memory_type_taxonomy_has_one_cross_package_identity() -> None:
    assert MemoryType is ArrayBridgeMemoryType
    assert RawConstantsMemoryType is ArrayBridgeMemoryType
    assert RuntimeMemoryType is ArrayBridgeMemoryType
    assert PipelineMemoryType is ArrayBridgeMemoryType


def test_legacy_openhcs_memory_type_pickle_resolves_to_owner_identity() -> None:
    legacy_payload = (
        b"copenhcs.constants.constants\nMemoryType\np0\n" b"(Vnumpy\np1\ntp2\nRp3\n."
    )

    assert pickle.loads(legacy_payload) is ArrayBridgeMemoryType.NUMPY
