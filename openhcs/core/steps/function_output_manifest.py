"""Execution-local main-flow output lineage for FunctionStep execution."""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import Iterator, Sequence
from weakref import WeakKeyDictionary

from polystore.streaming.identity import StreamProducerIdentity

from openhcs.core.source_path_identity import (
    source_path_identity,
    source_path_relative_to,
)
from openhcs.core.artifacts import ArtifactOutputPlan, ArtifactType, ImageArtifactType
from openhcs.core.aligned_image_payload import AlignedImageSliceContext
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.path_pattern_matching import PathPatternTemplateMatcher
from openhcs.core.runtime_array_values import RuntimeArrayData
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_metadata,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_metadata import DurableSourceMetadata, SourceMetadataValue

from openhcs.core.step_dependencies import StepInputDependencyKind
from openhcs.core.steps.function_output_identity import (
    FunctionOutputIdentity,
)
from openhcs.microscopes.microscope_interfaces import FilenameParser
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.source_bindings import CompiledSourceBindingPlan
from openhcs.core.source_binding_selection import (
    SourceBindingMatchedImageSet,
    SourcePatternResolutionContext,
)
from openhcs.core.source_matching import SourceImageSetIdentityPolicy
from openhcs.core.axes import AxisFamily, PartitionAxis


@dataclass(frozen=True, slots=True)
class StepOutputManifestKey:
    """Identity for main-flow files produced by one step for one axis."""

    step_scope_id: str
    axis_id: str


class NoStepOutputManifestMatch(RuntimeError):
    """Raised when a stale directory pattern is not in producer lineage."""


@dataclass(frozen=True, slots=True)
class ProducedOutputSemantics(FunctionOutputIdentity):
    """Semantic record for one output file produced by a FunctionStep."""

    producer_identity: StreamProducerIdentity
    output_path: str
    relative_output_path: str
    image_metadata: ImagePayloadMetadata | None = None
    main_flow_plane_axis: RuntimePlaneAxis | None = RuntimePlaneAxis.RUNTIME_SLICE

    def published(self) -> "ProducedOutputSemantics":
        """Fix the saved slot while retaining live provenance and storage aliases."""
        if isinstance(self.component_values, DurableSourceMetadata):
            return self
        return replace(
            self,
            component_values=DurableSourceMetadata.from_mapping(self.component_values),
            filename_component_values=self.filename_values,
        )

    def path_tokens(self, parser: FilenameParser) -> frozenset[str]:
        """Expose this occurrence's exact storage and unqualified address aliases."""
        tokens = {
            token
            for value in (self.relative_output_path, self.output_path)
            for token in (
                source_path_identity(value).as_posix(),
                source_path_identity(value).name,
            )
        }
        if self.filename_qualifier is not None:
            tokens.add(self.without_filename_qualifier().filename(parser))
        return frozenset(tokens)

    def passed_through(self, plan: CompiledStepPlan) -> "ProducedOutputSemantics":
        """Retain the image domain and physical identity under the next producer."""
        return replace(
            self,
            producer_identity=plan.producer_identity_for_main_flow(self.output_context),
            relative_output_path=source_path_identity(self.output_path).name,
        )

    def contextualize_image_payload(
        self,
        payload: RuntimeArrayData,
    ) -> RuntimeArrayData:
        """Attach this exact produced-output identity to a reloaded payload."""

        metadata = self.image_metadata or image_payload_metadata(payload)
        return metadata.with_source_component_metadata(
            self.component_metadata(metadata.source_component_metadata)
        ).attach_to(payload)

    def path_under(self, output_dir: str | Path) -> str:
        """Project this output's manifest-owned relative path under a new root."""

        return str(Path(output_dir) / self.relative_output_path)

    def memory_path(self, plan: CompiledStepPlan) -> str:
        """Resolve this original saved occurrence in its step's memory namespace."""
        path = Path(self.output_path)
        return str(path) if path.is_absolute() else self.path_under(plan.output_dir)

    def source_metadata_for_projection(
        self, metadata: ImagePayloadMetadata, destination: str
    ) -> dict[str, SourceMetadataValue]:
        """Combine this occurrence's coordinates with current persisted image facts."""
        source_metadata = dict(
            self.component_metadata(metadata.source_component_metadata)
        )
        metadata.source_voxel_spacing.merge_into(source_metadata, path=destination)
        return source_metadata

    def execution_scope(self, plan: CompiledStepPlan) -> RuntimeExecutionAxisScope:
        """Retain the exact producer coordinates of a whole intrinsic image."""
        group_component = plan.execution_group_scope.component
        group_value = (
            None
            if group_component is None
            else self.component_values.get(group_component.name)
        )
        return RuntimeExecutionAxisScope.from_raw(
            plan.axis_id,
            component=group_component if group_value is not None else None,
            value=group_value,
            fixed_component_values=tuple(
                (component, str(value))
                for component in AxisFamily.active().axes
                if not issubclass(component, PartitionAxis)
                and component is not group_component
                and (value := self.component_values.get(component.name)) is not None
            ),
        )

    def owns_persisted_artifact(
        self,
        output_plan: ArtifactOutputPlan,
        output_path: str,
        output_dir: str | Path,
    ) -> bool:
        """Identify the same declared producer and exact saved occurrence."""
        identity = self.producer_identity
        return (
            self.output_context.persisted_source_alias,
            identity.artifact_kind,
            identity.step_scope_id,
            Path(self.path_under(output_dir)),
        ) == (
            output_plan.name,
            output_plan.artifact_type.value,
            output_plan.producer_step_scope_id,
            Path(output_path),
        )

    @property
    def output_context(self) -> AlignedImageSliceContext:
        """Return the declared main-flow context for this produced output."""

        return AlignedImageSliceContext(
            output_kind=self.producer_identity.output_kind,
            output_key=self.producer_identity.output_key,
            projection_key=self.producer_identity.projection_key,
            artifact_kind=self.producer_identity.artifact_kind,
        )

    @property
    def main_flow_address(
        self,
    ) -> tuple[
        str,
        str,
        str | None,
        tuple[tuple[str, str | int], ...],
    ]:
        """Return the semantic main-flow slot occupied by this output."""

        return (
            self.producer_identity.output_kind,
            self.producer_identity.output_key,
            self.producer_identity.artifact_kind,
            tuple(sorted(self.component_values.items())),
        )

    @property
    def is_image_payload(self) -> bool:
        """Return whether image persistence and streaming own this output."""
        artifact_kind = self.producer_identity.artifact_kind
        if artifact_kind is None:
            return True
        return ArtifactType.coerce(artifact_kind) is ImageArtifactType

    @classmethod
    def from_output(
        cls,
        plan: CompiledStepPlan,
        output_path: str | Path,
        output_identity: FunctionOutputIdentity,
        output_context: AlignedImageSliceContext | None = None,
        image_metadata: ImagePayloadMetadata | None = None,
        main_flow_plane_axis: RuntimePlaneAxis | None = RuntimePlaneAxis.RUNTIME_SLICE,
    ) -> "ProducedOutputSemantics":
        output_path_text = str(output_path)
        if output_context is None:
            output_context = AlignedImageSliceContext.anonymous_main_flow()
        return cls(
            producer_identity=plan.producer_identity_for_main_flow(output_context),
            component_values=output_identity.component_values,
            extension=output_identity.extension,
            source=output_identity.source,
            filename_component_values=output_identity.filename_component_values,
            filename_qualifier=output_identity.filename_qualifier,
            output_path=output_path_text,
            relative_output_path=StepOutputManifestStore.relative_output_path(
                output_path_text,
                Path(plan.output_dir),
            ),
            image_metadata=image_metadata,
            main_flow_plane_axis=main_flow_plane_axis,
        )

    @classmethod
    def from_existing_main_flow_path(
        cls,
        plan: CompiledStepPlan,
        path: str | Path,
        parser: FilenameParser,
        *,
        output_context: AlignedImageSliceContext | None = None,
    ) -> "ProducedOutputSemantics":
        """Return producer lineage for an existing image path passed through a step."""
        path = Path(path)
        if output_context is None:
            output_context = AlignedImageSliceContext.anonymous_main_flow()
        parsed = parser.parse_filename(path.name)
        extension = parsed.extension if parsed is not None else path.suffix or None
        identity = FunctionOutputIdentity(
            component_values=(
                FunctionOutputIdentity.component_values_from_parsed(parsed)
                if parsed is not None
                else {}
            ),
            extension=extension,
            source="existing main-flow path",
        )
        return cls(
            producer_identity=plan.producer_identity_for_main_flow(output_context),
            component_values=identity.component_values,
            extension=identity.extension,
            source=identity.source,
            filename_component_values=identity.filename_component_values,
            filename_qualifier=identity.filename_qualifier,
            output_path=source_path_identity(str(path)).as_posix(),
            relative_output_path=source_path_identity(str(path)).name,
        )


@dataclass(slots=True)
class StepOutputManifestStore:
    """Execution-local main-flow output lineage for shared VFS directories."""

    records_by_key: dict[
        StepOutputManifestKey,
        dict[
            tuple[str, str, str | None, tuple[tuple[str, str | int], ...]],
            ProducedOutputSemantics,
        ],
    ] = field(default_factory=dict)
    own_output_counts: dict[StepOutputManifestKey, int] = field(default_factory=dict)
    selected_records_by_source: dict[
        StepOutputManifestKey,
        dict[
            tuple[frozenset[tuple[str, str, str | None]], bool],
            tuple[ProducedOutputSemantics, ...],
        ],
    ] = field(default_factory=dict)

    def begin_step(
        self,
        plan: CompiledStepPlan,
        input_records: Sequence[ProducedOutputSemantics] = (),
    ) -> None:
        key = self.key_for_producer(plan)
        if key is None:
            return
        records = {
            published.main_flow_address: published
            for record in input_records
            for published in (record.published(),)
        }
        self.records_by_key[key] = records
        self.own_output_counts[key] = sum(
            record.producer_identity.step_scope_id == key.step_scope_id
            for record in records.values()
        )
        self._invalidate_record_selection_caches(key)

    def record_outputs(
        self,
        plan: CompiledStepPlan,
        output_records: Sequence[ProducedOutputSemantics],
        *,
        collapsed_input_domain: bool = False,
    ) -> None:
        key = self.key_for_producer(plan)
        if key is None:
            return
        if not output_records:
            return
        records = self.records_by_key.setdefault(key, {})
        current_outputs = tuple(record.published() for record in output_records)
        own_output_count = self.own_output_counts.get(key, 0)
        if records and not own_output_count:
            if (
                collapsed_input_domain
                or plan.compiled_function_pattern.replaces_inherited_main_flow_domain
                or any(record.main_flow_address not in records for record in current_outputs)
            ):
                records.clear()
        for record in current_outputs:
            address = record.main_flow_address
            previous = records.get(address)
            if previous is not None:
                own_output_count -= (
                    previous.producer_identity.step_scope_id == key.step_scope_id
                )
            records[address] = record
            own_output_count += record.producer_identity.step_scope_id == key.step_scope_id
        self.own_output_counts[key] = own_output_count
        self._invalidate_record_selection_caches(key)

    def _invalidate_record_selection_caches(self, key: StepOutputManifestKey) -> None:
        self.selected_records_by_source.pop(key, None)

    def producer_records_for(
        self,
        plan: CompiledStepPlan,
    ) -> tuple[ProducedOutputSemantics, ...] | None:
        key = self._main_input_producer_key(plan)
        if key is None:
            return None
        return self.records_for_key(key)

    @staticmethod
    def _main_input_producer_key(
        plan: CompiledStepPlan,
    ) -> StepOutputManifestKey | None:
        dependency = plan.main_input_dependency
        if dependency.kind is not StepInputDependencyKind.STEP_OUTPUT:
            return None
        if dependency.source_step_scope_id is None:
            return None
        return StepOutputManifestKey(dependency.source_step_scope_id, plan.axis_id)

    def producer_paths_for(
        self,
        plan: CompiledStepPlan,
    ) -> tuple[str, ...] | None:
        records = self.producer_records_for(plan)
        if records is None:
            return None
        records = self._unique_output_path_records(records)
        return tuple(record.relative_output_path for record in records)

    def producer_patterns_by_execution_group(
        self,
        plan: CompiledStepPlan,
        patterns: Sequence[str],
        parser: FilenameParser,
    ) -> dict[str | None, tuple[str, ...]] | None:
        """Group producer pixels by semantic coordinates, not storage filenames."""
        records = self._selected_unique_producer_records_for(plan)
        if records is None:
            return None
        component = plan.execution_group_scope.component
        records_by_group: dict[str | None, list[ProducedOutputSemantics]] = {}
        for record in records:
            value = (
                None
                if component is None
                else record.component_values.get(component.name)
            )
            key = plan.execution_group_scope.normalize_key(value)
            if plan.execution_group_scope.contains_runtime_key(key):
                records_by_group.setdefault(key, []).append(record)
        patterns = tuple(dict.fromkeys(patterns))
        groups = {}
        for key, group_records in records_by_group.items():
            index = ProducedPathRecordIndex.from_records(group_records, parser)
            groups[key] = tuple(
                pattern for pattern in patterns if index.contains(pattern)
            )
        return groups

    def produced_records_for(
        self,
        plan: CompiledStepPlan,
    ) -> tuple[ProducedOutputSemantics, ...]:
        key = self.key_for_producer(plan)
        if key is None:
            return ()
        return self.records_for_key(key)

    def produced_paths_for(
        self,
        plan: CompiledStepPlan,
    ) -> tuple[str, ...]:
        return tuple(
            record.relative_output_path for record in self.produced_records_for(plan)
        )

    def image_records_for(
        self, plan: CompiledStepPlan
    ) -> tuple[ProducedOutputSemantics, ...]:
        """Select image occurrences directly from this step's current producer cohort."""
        return tuple(
            record
            for record in self.produced_records_for(plan)
            if record.is_image_payload
        )

    def producer_output_contexts_for_paths(
        self,
        plan: CompiledStepPlan,
        paths: Sequence[str],
        parser: FilenameParser,
    ) -> tuple[AlignedImageSliceContext, ...]:
        """Return producer output contexts aligned to concrete input paths."""

        records = self.producer_output_records_for_paths(plan, paths, parser)
        if records is None:
            return tuple(
                AlignedImageSliceContext.anonymous_main_flow() for _path in paths
            )
        return tuple(record.output_context for record in records)

    def producer_output_records_for_paths(
        self,
        plan: CompiledStepPlan,
        paths: Sequence[str],
        parser: FilenameParser,
    ) -> tuple[ProducedOutputSemantics, ...] | None:
        """Resolve exact producer declarations in the requested physical path order."""

        index = self.producer_record_index_for(plan, parser)
        return None if index is None else index.records_for_paths(paths)

    def producer_record_index_for(
        self,
        plan: CompiledStepPlan,
        parser: FilenameParser,
    ) -> ProducedPathRecordIndex | None:
        """Admit one current producer cohort with its correlated address aliases."""
        records = self._selected_unique_producer_records_for(plan, path_ordered=True)
        return (
            None
            if records is None
            else ProducedPathRecordIndex.from_records(records, parser)
        )

    def filter_to_producer_paths(
        self,
        plan: CompiledStepPlan,
        paths: Sequence[str],
        parser: FilenameParser,
    ) -> list[str]:
        index = self.producer_record_index_for(plan, parser)
        if index is None:
            return list(paths)
        selected = [path for path in paths if index.contains(path)]
        if selected:
            return selected
        if paths:
            raise NoStepOutputManifestMatch
        return []

    def _selected_unique_producer_records_for(
        self,
        plan: CompiledStepPlan,
        *,
        path_ordered: bool = False,
    ) -> tuple[ProducedOutputSemantics, ...] | None:
        producer_key = self._main_input_producer_key(plan)
        if producer_key is None:
            return None
        requested = self._requested_producer_outputs(plan)
        selections = self.selected_records_by_source.setdefault(producer_key, {})
        insertion_key = (requested, False)
        if insertion_key not in selections:
            producer_records = self.records_for_key(producer_key)
            selected = self._select_requested_producer_records(requested, producer_records)
            selections[insertion_key] = self._unique_output_path_records(selected)
        if not path_ordered:
            return selections[insertion_key]
        path_key = (requested, True)
        if path_key not in selections:
            selections[path_key] = tuple(
                sorted(selections[insertion_key], key=lambda record: record.output_path)
            )
        return selections[path_key]

    @staticmethod
    def _unique_output_path_records(
        records: Sequence[ProducedOutputSemantics],
    ) -> tuple[ProducedOutputSemantics, ...]:
        records_by_path: dict[str, ProducedOutputSemantics] = {}
        for record in records:
            existing = records_by_path.get(record.output_path)
            if (
                existing is not None
                and existing.main_flow_plane_axis is not record.main_flow_plane_axis
            ):
                raise ValueError(
                    "One produced output path cannot declare conflicting main-flow image axes: "
                    f"{record.output_path!r}."
                )
            records_by_path.setdefault(record.output_path, record)
        return tuple(records_by_path.values())

    def _select_requested_producer_records(
        self,
        requested: frozenset[tuple[str, str, str | None]],
        producer_records: Sequence[ProducedOutputSemantics],
    ) -> tuple[ProducedOutputSemantics, ...]:
        if not requested:
            return tuple(producer_records)
        selected = tuple(
            record
            for record in producer_records
            if (
                record.producer_identity.output_kind,
                record.producer_identity.output_key,
                record.producer_identity.artifact_kind,
            )
            in requested
        )
        if selected:
            return selected
        if all(
            AlignedImageSliceContext(
                output_kind=record.producer_identity.output_kind,
                output_key=record.producer_identity.output_key,
                projection_key=record.producer_identity.projection_key,
                artifact_kind=record.producer_identity.artifact_kind,
            ).is_anonymous_main_flow
            for record in producer_records
        ):
            return tuple(producer_records)
        raise NoStepOutputManifestMatch

    @staticmethod
    def _requested_producer_outputs(
        plan: CompiledStepPlan,
    ) -> frozenset[tuple[str, str, str | None]]:
        dependency = plan.main_input_dependency
        if (
            dependency.kind is not StepInputDependencyKind.STEP_OUTPUT
            or dependency.source_step_scope_id is None
        ):
            return frozenset()
        producer_scope_id = dependency.source_step_scope_id
        return frozenset(
            (
                AlignedImageSliceContext.MAIN_FLOW_OUTPUT_KIND,
                edge.spec.name,
                edge.spec.artifact_type.value,
            )
            for invocation in plan.compiled_function_pattern.iter_invocations()
            for edge in invocation.artifact_input_edges
            if (
                edge.main_flow_projection is not None
                or (
                    edge.spec.parameter_name is None
                    and edge.spec.ref()
                    in invocation.contract.output_group_scope_sources
                    and edge.storage_plan is not None
                    and edge.storage_plan.source_step_scope_id == producer_scope_id
                )
            )
        )

    def records_for_key(
        self,
        key: StepOutputManifestKey,
    ) -> tuple[ProducedOutputSemantics, ...]:
        return tuple(self.records_by_key.get(key, {}).values())

    @staticmethod
    def key_for_producer(
        plan: CompiledStepPlan,
    ) -> StepOutputManifestKey | None:
        if not plan.step_scope_id:
            return None
        return StepOutputManifestKey(plan.step_scope_id, plan.axis_id)

    @staticmethod
    def relative_output_path(output_path: str, output_dir: Path) -> str:
        return source_path_relative_to(output_path, str(output_dir))


_STEP_OUTPUT_MANIFESTS: WeakKeyDictionary[
    ProcessingContext,
    StepOutputManifestStore,
] = WeakKeyDictionary()


def step_output_manifest(context: ProcessingContext) -> StepOutputManifestStore:
    """Return execution-local main-flow output lineage for a context."""
    if context in _STEP_OUTPUT_MANIFESTS:
        return _STEP_OUTPUT_MANIFESTS[context]
    manifest = StepOutputManifestStore()
    _STEP_OUTPUT_MANIFESTS[context] = manifest
    return manifest


@dataclass(frozen=True, slots=True)
class ProducedPathRecordIndex:
    """Correlated producer occurrences and their concrete/template address aliases."""

    records: tuple[ProducedOutputSemantics, ...]
    record_indices_by_token: dict[str, tuple[int, ...]]

    @classmethod
    def from_records(
        cls,
        records: Sequence[ProducedOutputSemantics],
        parser: FilenameParser,
    ) -> ProducedPathRecordIndex:
        indices_by_token: dict[str, list[int]] = {}
        for index, record in enumerate(records):
            for token in record.path_tokens(parser):
                indices_by_token.setdefault(token, []).append(index)
        return cls(
            records=tuple(records),
            record_indices_by_token={
                token: tuple(indices) for token, indices in indices_by_token.items()
            },
        )

    def matching_tokens(self, path: str) -> Iterator[str]:
        """Resolve exact and template address aliases through the existing matcher."""
        path = source_path_identity(path).as_posix()
        tokens = self.record_indices_by_token
        matcher = PathPatternTemplateMatcher.from_pattern(path)
        if path in tokens:
            yield path
        if matcher is not None:
            for token in tokens:
                if token != path and matcher.matches(token):
                    yield token

    def contains(self, path: str) -> bool:
        return next(self.matching_tokens(path), None) is not None

    def matching_records(self, path: str) -> tuple[ProducedOutputSemantics, ...]:
        indices = sorted(
            {
                index
                for token in self.matching_tokens(path)
                for index in self.record_indices_by_token[token]
            }
        )
        return tuple(self.records[index] for index in indices)

    def record_for_path(self, path: str) -> ProducedOutputSemantics:
        """Require one original occurrence for one admitted physical address."""
        records = self.matching_records(path)
        if len(records) != 1:
            raise NoStepOutputManifestMatch(
                "Expected one producer output context for input path "
                f"{path!r}, found {len(records)}."
            )
        return records[0]

    def records_for_paths(
        self,
        paths: Sequence[str],
    ) -> tuple[ProducedOutputSemantics, ...]:
        return tuple(self.record_for_path(path) for path in paths)

    def source_binding_members(
        self,
        paths: Sequence[str],
        *,
        source_bindings: CompiledSourceBindingPlan,
        identity_policy: SourceImageSetIdentityPolicy,
        parser: FilenameParser,
    ) -> tuple[ProducedOutputSemantics, ...]:
        """Expand aliases only within this exact predecessor's current outputs."""
        anchors = tuple(record.output_path for record in self.records_for_paths(paths))
        bindings = source_bindings.primary_plane_bindings
        if not bindings:
            return self.records_for_paths(anchors)
        source_context = SourcePatternResolutionContext.from_sources(
            parser=parser,
            source_paths_by_virtual_path={},
            source_metadata_by_path={
                record.output_path: (
                    record.component_values
                    if record.image_metadata is None
                    else record.source_metadata_for_projection(
                        record.image_metadata, record.output_path
                    )
                )
                for record in self.records
            },
            metadata_rules=source_bindings.metadata_rules,
        )
        members = SourceBindingMatchedImageSet.from_plan(
            bindings=bindings,
            match_plan=source_bindings.match_plan,
            source_context=source_context,
            identity_policy=identity_policy,
        ).expand(
            anchors,
            source_universe=tuple(record.output_path for record in self.records),
        )
        return self.records_for_paths(members)

    def validate_input_records(
        self,
        records: Sequence[ProducedOutputSemantics],
    ) -> None:
        """Validate address cardinality while retaining the already-selected cohort."""
        for record in records:
            self.record_for_path(record.output_path)
