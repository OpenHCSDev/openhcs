"""CellProfiler plugin EnforceObjectsOneToOne.

Upstream: CellProfiler-plugins ``active_plugins/enforceobjectsonetoone.py``, as
run by CellProfiler 4.2.8.1 with NumPy 1.24.

The plugin takes two independently made object sets, the pre-primary objects
(nuclei, say) and the pre-secondary objects (cells), and keeps the pairs in
which a pre-primary object is the best one on a pre-secondary object. The kept
pre-primary objects, cut down to their partner, are the primary objects; the
kept pre-secondary objects, whole, are the secondary objects.

What the plugin does, reproduced here:

* An object's candidates are the partners it shares pixels with, the largest
  shared area first, equal areas in label order. It takes the first candidate
  on which it is the best object.
* The best object on a partner is the one with the largest share of its
  partnered area there: the shared area divided by the object's area on any
  partner, not by the object's whole area. An object that touches one partner
  only therefore always scores 1, however little of it lies on the partner.
  Equal scores go to the larger shared area; when that is equal too, the
  partner has no best object. (The plugin's shortcut for a partner touched by
  one object compares a shape with a number, is never taken, and would give the
  same result.)
* Pre-primary objects are matched first. One without a match is removed; a
  matched one loses every pixel outside its partner. The remaining labels are
  renumbered 1..N in ascending order of the old ones.
* Pre-secondary objects are then matched in the same way against the new
  primary objects and keep their whole shape. Both sets are numbered in the
  order of their own old labels, so primary object 3 need not lie in secondary
  object 3; the parent measurements say which belongs to which.
* The plugin takes the smallest value of a label image for the background. In
  an object set that covers every pixel, the object with the lowest number is
  therefore never visited: it is neither matched nor removed, and it is made
  background by the renumbering unless a removed object left background before
  it.
* When either set has no objects, both outputs are that empty set.

The functions return the two object sets and three parent-child relationships:
pre-primary to primary, pre-secondary to secondary, and primary to secondary
(the parent is the object a child overlaps most, the lowest number among
equals). Counts, locations and the ``Parent_`` and ``Children_..._Count``
measurements are made from them by the module family when the objects are
recorded; because the labels have no gaps, they are CellProfiler's.

Refused, because the CellProfiler plugin fails:

* neither set is empty and no object finds a partner (the plugin takes the
  maximum of an empty array). This includes sets that do not overlap, and sets
  in which every partner is contested by objects with equal scores and areas;
* the two outputs do not hold the same numbers (the plugin's own final check),
  which happens only with a set that covers every pixel;
* two non-empty sets of different shapes.

The block's display option and the image named for it only choose what the
plugin's window shows. With the option on, the plugin still fetches that image
after it has stored its results and fails when the image is missing or colour;
that is not reproduced: the image is not an input here.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import numpy as np

from openhcs.core.artifacts.kinds import ObjectLabelsArtifactType
from openhcs.core.artifacts.relations import SourceStackLineageSourceRelation
from openhcs.core.artifacts.specs import ArtifactSpecCollection
from openhcs.core.measurement_row_materialization import (
    MeasurementSparseColumnarRows,
)
from openhcs.core.memory.decorators import numpy
from openhcs.core.pipeline.function_contracts import (
    FullStackLabels,
    object_label_input_execution_mode,
    special_inputs,
)
from openhcs.core.processing_contracts import Pure2DContract, Pure3DContract
from openhcs.core.runtime_object_label_domains import (
    PresentObjectLabelIdsDomainDeclaration,
)
from openhcs.core.runtime_object_labels import (
    ObjectLabelValue,
    object_label_dense_array,
    object_label_value_with_dense_labels,
)
from openhcs.core.runtime_relationships import (
    DirectedObjectRelationshipPayload,
    object_label_parent_child_payload,
)
from openhcs.interop.cellprofiler.module_artifact_declarations import (
    MeasurementArtifactOutputModule,
    ObjectArtifactInputModule,
    ObjectArtifactOutputModule,
    ParentChildLineageArtifactOutputModule,
    PlaneRuntimeArtifactModule,
)
from openhcs.interop.cellprofiler.runtime.primary_image_input_policies import (
    ObjectLabelDrivenPrimaryImageInputPolicy,
)
from openhcs.interop.cellprofiler.settings_binder import SettingToKeywordBinding
from openhcs.processing.backends.cellprofiler.morphology import (
    ZStackFunctionVariantModule,
)

if TYPE_CHECKING:
    from openhcs.core.artifacts.relations import ArtifactSpecRelation
    from openhcs.core.artifacts.specs import ArtifactSpec
    from openhcs.core.function_patterns import FunctionInvocationKey
    from openhcs.core.invocation_artifacts import ArtifactDeclarationStepContext
    from openhcs.interop.cellprofiler.parser import ModuleBlock

_PLUGIN_FAILS = "the CellProfiler plugin fails"

OneToOneObjects = tuple[
    np.ndarray,
    MeasurementSparseColumnarRows,
    ObjectLabelValue,
    ObjectLabelValue,
    DirectedObjectRelationshipPayload,
    DirectedObjectRelationshipPayload,
    DirectedObjectRelationshipPayload,
]


def _refuse(reason: str) -> ValueError:
    return ValueError(
        f"EnforceObjectsOneToOne cannot run: {reason}; {_PLUGIN_FAILS} here."
    )


def _visited_labels(labels: np.ndarray) -> np.ndarray:
    """The labels the plugin takes for objects: all values but the smallest.

    The smallest is the background, 0, unless the objects cover every pixel.
    """
    return np.unique(labels)[1:]


def _partner_of_each(objects: np.ndarray, partners: np.ndarray) -> np.ndarray:
    """The partner of every object label (index), 0 where it has none."""
    partner_columns = int(partners.max()) + 1
    shared = np.bincount(
        objects.ravel().astype(np.int64) * partner_columns + partners.ravel(),
        minlength=(int(objects.max()) + 1) * partner_columns,
    ).reshape(-1, partner_columns)[1:, 1:]
    touching = shared > 0
    area_on_partners = shared.sum(axis=1, keepdims=True)
    score = np.where(touching, shared / np.maximum(area_on_partners, 1), -1.0)
    best = touching & (score == score.max(axis=0, initial=-1.0))
    # Among equal scores the larger shared area wins, and nobody when equal.
    area_of_best = np.where(best, shared, 0)
    winning = best & (area_of_best == area_of_best.max(axis=0, initial=0))
    won = winning & (winning.sum(axis=0) == 1)
    # The largest shared area first; argmax takes the lowest label of equals.
    area_won = np.where(won, shared, 0)
    partner_of = np.zeros(shared.shape[0] + 1, dtype=np.int64)
    if area_won.size:
        partner_of[1:] = np.where(area_won.any(axis=1), area_won.argmax(axis=1) + 1, 0)
    return partner_of


def _renumbered(labels: np.ndarray) -> np.ndarray:
    """Labels 1..N in ascending order of the old ones."""
    present = _visited_labels(labels)
    new_label = np.zeros(int(labels.max()) + 1, dtype=np.int64)
    new_label[present] = np.arange(1, len(present) + 1)
    return new_label[labels]


def _matched(objects: np.ndarray, partners: np.ndarray, *, cut: bool) -> np.ndarray:
    """The objects that found a partner, renumbered; cut down to it on request."""
    partner_of = _partner_of_each(objects, partners)
    visited = np.zeros(len(partner_of), dtype=bool)
    visited[_visited_labels(objects)] = True
    if not partner_of[visited].any():
        raise _refuse("no object is matched")
    partner = partner_of[objects]
    removed = partner == 0
    if cut:
        removed |= partners != partner
    return _renumbered(np.where(visited[objects] & removed, 0, objects))


def _one_to_one(
    pre_primary: np.ndarray, pre_secondary: np.ndarray
) -> tuple[np.ndarray, np.ndarray]:
    """The primary and secondary labels the plugin stores."""
    if not pre_secondary.any():
        return pre_secondary, pre_secondary
    if not pre_primary.any():
        return pre_primary, pre_primary
    if pre_primary.shape != pre_secondary.shape:
        raise _refuse(
            f"the pre-primary objects have shape {pre_primary.shape} and the "
            f"pre-secondary objects {pre_secondary.shape}"
        )
    primary = _matched(pre_primary, pre_secondary, cut=True)
    secondary = _matched(pre_secondary, primary, cut=False)
    if not np.array_equal(np.unique(primary), np.unique(secondary)):
        raise _refuse(
            f"{len(np.unique(primary)) - 1} primary and "
            f"{len(np.unique(secondary)) - 1} secondary objects are left"
        )
    return primary, secondary


def _as_parents_and_children(
    image: np.ndarray,
    pre_primary_labels: ObjectLabelValue,
    pre_secondary_labels: ObjectLabelValue,
) -> OneToOneObjects:
    primary_array, secondary_array = _one_to_one(
        object_label_dense_array(pre_primary_labels, dtype=np.int32),
        object_label_dense_array(pre_secondary_labels, dtype=np.int32),
    )
    primary = object_label_value_with_dense_labels(
        pre_primary_labels,
        primary_array.astype(np.int32),
        domain_declaration=PresentObjectLabelIdsDomainDeclaration(),
    )
    secondary = object_label_value_with_dense_labels(
        pre_secondary_labels,
        secondary_array.astype(np.int32),
        domain_declaration=PresentObjectLabelIdsDomainDeclaration(),
    )
    return (
        image,
        # Counts, locations and parents are measured from the labels when the
        # objects are recorded; the function has no measurements of its own.
        MeasurementSparseColumnarRows.from_rows((), fields=()),
        primary,
        secondary,
        object_label_parent_child_payload(pre_primary_labels, primary),
        object_label_parent_child_payload(pre_secondary_labels, secondary),
        object_label_parent_child_payload(primary, secondary),
    )


@numpy(contract=Pure2DContract)
@special_inputs("pre_primary_labels", "pre_secondary_labels")
def enforce_objects_one_to_one(
    image: np.ndarray,
    pre_primary_labels: ObjectLabelValue,
    pre_secondary_labels: ObjectLabelValue,
) -> OneToOneObjects:
    """Pair two object sets of a plane one to one, as nuclei with their cells.

    Keeps the pairs in which a pre-primary object is the best one on a
    pre-secondary object it overlaps: the one with the largest share of its
    partnered area there, the larger overlap among equal shares. Unpaired
    objects of both sets are dropped. The primary objects are the paired
    pre-primary objects without their pixels outside the partner; the secondary
    objects are the paired pre-secondary objects, unchanged in shape. Both are
    renumbered from 1 in the order of their old numbers.

    The primary objects are children of the pre-primary objects, the secondary
    objects children of the pre-secondary and of the primary objects.

    Reproduces the CellProfiler plugin EnforceObjectsOneToOne and fails where
    it does: when neither set is empty and nothing can be paired.

    Args:
        pre_primary_labels: The inner objects (nuclei), made on their own.
        pre_secondary_labels: The outer objects (cells), made on their own.
    """
    return _as_parents_and_children(image, pre_primary_labels, pre_secondary_labels)


@numpy(contract=Pure3DContract)
@object_label_input_execution_mode(FullStackLabels)
@special_inputs("pre_primary_labels", "pre_secondary_labels")
def enforce_objects_one_to_one_3d(
    image: np.ndarray,
    pre_primary_labels: ObjectLabelValue,
    pre_secondary_labels: ObjectLabelValue,
) -> OneToOneObjects:
    """Pair two object sets of a volume one to one, as nuclei with their cells.

    The volume counterpart of ``enforce_objects_one_to_one``: overlaps are
    counted in voxels over all planes.

    Args:
        pre_primary_labels: Volume of the inner objects (nuclei).
        pre_secondary_labels: Volume of the outer objects (cells).
    """
    return _as_parents_and_children(image, pre_primary_labels, pre_secondary_labels)


class EnforceObjectsOneToOneModule(
    ZStackFunctionVariantModule,
    ObjectLabelDrivenPrimaryImageInputPolicy,
    PlaneRuntimeArtifactModule,
    ParentChildLineageArtifactOutputModule,
    MeasurementArtifactOutputModule,
    ObjectArtifactInputModule,
    ObjectArtifactOutputModule,
):
    module_name = "EnforceObjectsOneToOne"
    function_name = "enforce_objects_one_to_one"
    function_variants = ("enforce_objects_one_to_one_3d",)
    validated = True
    pre_primary_binding = SettingToKeywordBinding.input(
        "Pre-primary objects",
        ObjectLabelsArtifactType,
        runtime_parameter_name="pre_primary_labels",
    )
    pre_secondary_binding = SettingToKeywordBinding.input(
        "Pre-secondary objects",
        ObjectLabelsArtifactType,
        runtime_parameter_name="pre_secondary_labels",
    )
    primary_binding = SettingToKeywordBinding.output(
        "Name the output primary object", ObjectLabelsArtifactType
    )
    secondary_binding = SettingToKeywordBinding.output(
        "Name the output secondary object", ObjectLabelsArtifactType
    )
    setting_bindings = (
        pre_primary_binding,
        pre_secondary_binding,
        primary_binding,
        secondary_binding,
    )
    # Both only choose what the plugin's window shows.
    ignored_settings = (
        "In module display, show enforced objects on a selected image?",
        "Select the image for visualization",
    )

    @classmethod
    def primary_image_domain_input_binding(cls) -> SettingToKeywordBinding:
        return cls.pre_primary_binding

    @classmethod
    def _input_objects(
        cls,
        module: ModuleBlock,
        binding: SettingToKeywordBinding,
        artifact_inputs: ArtifactSpecCollection,
    ) -> ArtifactSpec:
        (name,) = cls.artifact_names_for_binding(module, binding)
        return artifact_inputs.require_by_name_and_artifact_type(
            name, ObjectLabelsArtifactType
        )

    @classmethod
    def artifact_output_relations(
        cls,
        module: ModuleBlock,
        *,
        binding: SettingToKeywordBinding,
        name: str,
        invocation_key: FunctionInvocationKey,
        step_context: ArtifactDeclarationStepContext,
        artifact_inputs: ArtifactSpecCollection,
        output_position: int,
    ) -> tuple[ArtifactSpecRelation, ...]:
        """Each output set comes from the input set it is a selection of."""
        made_from = {
            cls.primary_binding: cls.pre_primary_binding,
            cls.secondary_binding: cls.pre_secondary_binding,
        }
        if binding not in made_from:
            return super().artifact_output_relations(
                module,
                binding=binding,
                name=name,
                invocation_key=invocation_key,
                step_context=step_context,
                artifact_inputs=artifact_inputs,
                output_position=output_position,
            )
        source = cls._input_objects(module, made_from[binding], artifact_inputs)
        return (SourceStackLineageSourceRelation(source=source.ref()),)

    @classmethod
    def artifact_contract_outputs(
        cls,
        module: ModuleBlock,
        *,
        invocation_key: FunctionInvocationKey,
        step_context: ArtifactDeclarationStepContext,
        artifact_inputs: ArtifactSpecCollection,
    ) -> tuple[ArtifactSpec, ...]:
        """The declared outputs, then the three relationships the plugin measures."""
        outputs = ArtifactSpecCollection(
            super().artifact_contract_outputs(
                module,
                invocation_key=invocation_key,
                step_context=step_context,
                artifact_inputs=artifact_inputs,
            )
        )
        pre_primary = cls._input_objects(
            module, cls.pre_primary_binding, artifact_inputs
        )
        pre_secondary = cls._input_objects(
            module, cls.pre_secondary_binding, artifact_inputs
        )
        primary, secondary = (
            outputs.require_by_name_and_artifact_type(name, ObjectLabelsArtifactType)
            for binding in (cls.primary_binding, cls.secondary_binding)
            for name in cls.artifact_names_for_binding(module, binding)
        )
        return (
            *outputs.specs,
            *(
                cls.parent_child_relationship_output_artifact(
                    module,
                    step_context=step_context,
                    parent=parent,
                    child=child,
                    lineage_source=pre_primary,
                )
                for parent, child in (
                    (pre_primary, primary),
                    (pre_secondary, secondary),
                    (primary, secondary),
                )
            ),
        )
