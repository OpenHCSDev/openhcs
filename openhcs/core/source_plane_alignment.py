"""Source-plane identity alignment for runtime payload sequences."""

from __future__ import annotations

from dataclasses import dataclass
from typing import ClassVar

from openhcs.core.source_matching import (
    SourceImageSetIdentity,
    SourceImageSetIdentityCompatibility,
    SourceImageSetIdentityPairPredicate,
)

SourcePlaneIdentitySequence = tuple[frozenset[SourceImageSetIdentity], ...]


@dataclass(frozen=True, slots=True)
class SourcePlaneIdentitySequenceAlignment:
    """Align target source planes to an image source-plane sequence."""

    image_identities: SourcePlaneIdentitySequence
    target_identities: SourcePlaneIdentitySequence
    identity_predicate_type: ClassVar[type[SourceImageSetIdentityPairPredicate]] = (
        SourceImageSetIdentityCompatibility
    )

    def target_index_for_image_plane(
        self,
        image_identity: frozenset[SourceImageSetIdentity],
        *,
        used: frozenset[int] = frozenset(),
    ) -> int | None:
        if not image_identity:
            return None
        matches = tuple(
            index
            for index, target_identity in enumerate(self.target_identities)
            if (
                index not in used
                and self.identity_predicate_type.any_match(
                    target_identity,
                    image_identity,
                )
            )
        )
        if len(matches) != 1:
            return None
        return matches[0]

    def target_indexes_for_image_planes(self) -> tuple[int, ...] | None:
        indexes: list[int] = []
        used: set[int] = set()
        for image_identity in self.image_identities:
            match = self.target_index_for_image_plane(
                image_identity,
                used=frozenset(used),
            )
            if match is None:
                return None
            used.add(match)
            indexes.append(match)
        return tuple(indexes)

    def target_indexes_for_exact_axis(self) -> tuple[int, ...] | None:
        """Return a bijection only when both sequences describe one exact axis."""
        if not self.image_identities or len(self.image_identities) != len(
            self.target_identities
        ):
            return None
        return self.target_indexes_for_image_planes()

    @classmethod
    def unaligned_axis_indexes(
        cls,
        axes: tuple[SourcePlaneIdentitySequence, ...],
    ) -> tuple[int, ...]:
        """Return indexes that do not share one known image-set axis."""
        known = tuple(bool(axis) for axis in axes)
        if not any(known):
            return ()
        if not all(known):
            return tuple(index for index, present in enumerate(known) if not present)
        reference = axes[0]
        return tuple(
            index
            for index, target in enumerate(axes[1:], start=1)
            if cls(reference, target).target_indexes_for_exact_axis() is None
        )
