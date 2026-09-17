"""Prepare blinded authoring bundles from declaration-owned validation sources."""

from __future__ import annotations

import csv
import hashlib
import json
import os
import shutil
import zipfile
import zlib
from dataclasses import asdict, dataclass, is_dataclass
from datetime import UTC, datetime
from enum import Enum
from pathlib import Path
from typing import Any

from benchmark.contracts.dataset import DatasetSpec
from benchmark.contracts.validation import (
    FrozenPipelineReceipt,
    IndependentValidationSpec,
    PreparedValidationCorpus,
    ValidationArtifactKind,
    ValidationImageRecord,
    ValidationReferenceRecord,
    ValidationSourceSetSelection,
)
from benchmark.datasets.acquire import (
    DatasetArchiveMaterializer,
    DatasetFileDownloader,
)
from benchmark.datasets.registry import get_dataset_spec
from benchmark.validation.layouts import ValidationCorpusLayoutStrategy
from benchmark.validation.references import ValidationReferenceStrategy
from openhcs.constants import AllComponents, Microscope
from openhcs.core.config import LazySourceBindingsConfig, PipelineConfig
from openhcs.core.source_bindings import (
    ComponentSelector,
    ImportedMetadataJoin,
    ImportedMetadataTable,
    MetadataExtractionRule,
    MetadataSelector,
    MetadataSource,
    NamedSourceBinding,
    SourceBindingMatchDimension,
    SourceBindingMatchField,
    SourceBindingMatchMethod,
    SourceBindingMatchPlan,
    SourceBindingOrigin,
    SourceBindingsConfig,
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
    SourceSelector,
)


class ValidationCorpusPreparationError(RuntimeError):
    """Raised when a blind validation corpus cannot be prepared safely."""


@dataclass(frozen=True, slots=True)
class ValidationDslContract:
    """Derived OpenHCS reasoning surface for one prepared authoring bundle."""

    source_components: tuple[str, ...]
    grouping_fields: tuple[str, ...]
    variable_components: tuple[str, ...]
    source_set_count: int
    source_plane_count: int
    compiled_transitions: tuple[str, ...]


class ValidationCorpusPreparer:
    """Acquire, verify, normalize, and separate one validation dataset."""

    def __init__(
        self,
        *,
        downloader: DatasetFileDownloader | None = None,
        archive_materializer: DatasetArchiveMaterializer | None = None,
    ) -> None:
        self.downloader = downloader or DatasetFileDownloader()
        self.archive_materializer = archive_materializer or DatasetArchiveMaterializer()

    def prepare(
        self,
        dataset_id: str,
        *,
        output_root: Path,
        cache_root: Path,
    ) -> PreparedValidationCorpus:
        """Prepare a new authoring/scoring corpus; never overwrite an existing one."""

        spec = get_dataset_spec(dataset_id)
        validation = self._validation_spec(spec)
        dataset_root = Path(output_root).expanduser().resolve() / dataset_id
        if dataset_root.exists():
            raise FileExistsError(
                f"Validation corpus already exists: {dataset_root}. "
                "Use a new output root to preserve prior attempts."
            )

        source_root, raw_root = self._acquire(
            validation,
            cache_root=Path(cache_root).expanduser().resolve(),
        )
        layout = ValidationCorpusLayoutStrategy.for_layout(validation.layout)
        records, references = layout.normalize(raw_root, validation)
        development_records, held_out_records = split_validation_records(
            validation,
            records,
        )
        held_out_source_set_ids = {record.source_set_id for record in held_out_records}
        held_out_references = tuple(
            reference
            for reference in references
            if reference.source_set_id in held_out_source_set_ids
        )
        authoring_root = dataset_root / "authoring"
        held_out_root = dataset_root / "frozen_execution"
        scoring_root = dataset_root / "trusted_scoring"
        authoring_root.mkdir(parents=True)
        held_out_root.mkdir(parents=True)
        scoring_root.mkdir(parents=True)

        self._materialize_images(raw_root, authoring_root, development_records)
        self._materialize_images(raw_root, held_out_root, held_out_records)
        source_manifest_path = authoring_root / "source_manifest.csv"
        self._write_source_manifest(source_manifest_path, development_records)
        self._write_source_manifest(
            held_out_root / "source_manifest.csv",
            held_out_records,
        )
        self._write_source_manifest(
            scoring_root / "source_manifest.csv",
            held_out_records,
        )
        self._materialize_references(raw_root, scoring_root, held_out_references)
        self._write_reference_manifest(
            scoring_root / "reference_manifest.csv",
            held_out_references,
        )

        source_bindings = source_bindings_for_validation(validation)
        source_bindings_path = authoring_root / "source_bindings.py"
        self._write_source_bindings(source_bindings_path, source_bindings)
        pipeline_template_path = authoring_root / "pipeline_template.py"
        self._write_pipeline_template(
            pipeline_template_path,
            source_bindings,
        )
        self._write_source_bindings(
            held_out_root / "source_bindings.py",
            source_bindings,
        )
        dsl_contract = derive_validation_dsl_contract(
            validation,
            development_records,
        )
        self._write_authoring_guide(
            authoring_root / "OPENHCS_AUTHORING.md",
            spec,
            validation,
            dsl_contract,
        )

        provenance_path = dataset_root / "provenance.json"
        provenance_path.write_text(
            json.dumps(
                {
                    "dataset_id": dataset_id,
                    "record_url": validation.record_url,
                    "evidence_kind": validation.evidence_kind.value,
                    "layout": validation.layout.value,
                    "metric_profile": validation.metric_profile.value,
                    "licence": {
                        "name": validation.licence_name,
                        "url": validation.licence_url,
                    },
                    "source_root": str(source_root),
                    "raw_root": str(raw_root),
                    "artifacts": [
                        _json_value(artifact) for artifact in validation.artifacts
                    ],
                    "repository_sources": [
                        _json_value(source) for source in validation.repository_sources
                    ],
                    "reference_decoder": {
                        "url": validation.reference_decoder_url,
                        "revision": validation.reference_decoder_revision,
                    },
                    "partition_counts": _partition_counts(records),
                    "input_plane_count": len(records),
                    "reference_count": len(references),
                    "trial_split": _json_value(validation.trial_split),
                    "development": {
                        "source_set_count": len(
                            {record.source_set_id for record in development_records}
                        ),
                        "input_plane_count": len(development_records),
                        "source_set_ids": sorted(
                            {record.source_set_id for record in development_records}
                        ),
                    },
                    "held_out": {
                        "source_set_count": len(held_out_source_set_ids),
                        "input_plane_count": len(held_out_records),
                        "reference_count": len(held_out_references),
                        "source_set_ids": sorted(held_out_source_set_ids),
                    },
                    "derived_surfaces": {
                        "authoring": {
                            "source_manifest_sha256": _sha256(
                                authoring_root / "source_manifest.csv"
                            ),
                            "source_bindings_sha256": _sha256(
                                authoring_root / "source_bindings.py"
                            ),
                            "pipeline_template_sha256": _sha256(
                                authoring_root / "pipeline_template.py"
                            ),
                        },
                        "frozen_execution": {
                            "source_manifest_sha256": _sha256(
                                held_out_root / "source_manifest.csv"
                            ),
                            "source_bindings_sha256": _sha256(
                                held_out_root / "source_bindings.py"
                            ),
                        },
                        "trusted_scoring": {
                            "source_manifest_sha256": _sha256(
                                scoring_root / "source_manifest.csv"
                            ),
                            "reference_manifest_sha256": _sha256(
                                scoring_root / "reference_manifest.csv"
                            ),
                        },
                    },
                    "authoring_tracks": [
                        _json_value(track) for track in validation.authoring_tracks
                    ],
                    "published_assay_references": [
                        _json_value(reference)
                        for reference in validation.published_assay_references
                    ],
                    "dsl_contract": _json_value(dsl_contract),
                    "blindness_boundary": (
                        "Only authoring/ is supplied before pipeline freeze. "
                        "frozen_execution/ is disclosed after freeze for unchanged "
                        "execution; trusted_scoring/ remains evaluator-only."
                    ),
                },
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        return PreparedValidationCorpus(
            dataset_id=dataset_id,
            root=dataset_root,
            authoring_root=authoring_root,
            held_out_root=held_out_root,
            scoring_root=scoring_root,
            source_manifest_path=source_manifest_path,
            source_bindings_path=source_bindings_path,
            pipeline_template_path=pipeline_template_path,
            provenance_path=provenance_path,
        )

    def _acquire(
        self,
        validation: IndependentValidationSpec,
        *,
        cache_root: Path,
    ) -> tuple[Path, Path]:
        accession = validation.record_url.rstrip("/").rsplit("/", 1)[-1]
        source_root = cache_root / "sources" / accession
        materialization_key = hashlib.sha256(
            "\n".join(
                f"{artifact.name}:{artifact.sha256}"
                for artifact in validation.artifacts
            ).encode("utf-8")
        ).hexdigest()[:16]
        raw_root = cache_root / "materialized" / accession / materialization_key
        source_root.mkdir(parents=True, exist_ok=True)
        raw_root.mkdir(parents=True, exist_ok=True)

        for artifact in validation.artifacts:
            source_path = source_root / artifact.name
            if not source_path.is_file():
                self.downloader.download(artifact.url, source_path)
            _verify_artifact(source_path, artifact.size_bytes, artifact.sha256)
            if artifact.kind is ValidationArtifactKind.ZIP_ARCHIVE:
                self.archive_materializer.extract_missing_members(source_path, raw_root)
                _verify_materialized_archive(source_path, raw_root)
            else:
                target = raw_root / artifact.name
                if not target.is_file():
                    shutil.copy2(source_path, target)
                _verify_artifact(target, artifact.size_bytes, artifact.sha256)
        return source_root, raw_root

    @staticmethod
    def _validation_spec(spec: DatasetSpec) -> IndependentValidationSpec:
        validation = spec.independent_validation
        if validation is None:
            raise ValidationCorpusPreparationError(
                f"Dataset {spec.id!r} has no independent-validation declaration."
            )
        return validation

    @staticmethod
    def _materialize_images(
        raw_root: Path,
        destination_root: Path,
        records: tuple[ValidationImageRecord, ...],
    ) -> None:
        for record in records:
            source = raw_root / record.source_relative_path
            target = destination_root / record.canonical_relative_path
            _hardlink_or_copy(source, target)

    @staticmethod
    def _materialize_references(
        raw_root: Path,
        scoring_root: Path,
        records: tuple[ValidationReferenceRecord, ...],
    ) -> None:
        for record in records:
            source = raw_root / record.source_relative_path
            target = scoring_root / record.canonical_relative_path
            if target.exists():
                raise FileExistsError(
                    f"Normalized validation references collide at {target}."
                )
            ValidationReferenceStrategy.for_evidence(record.reference_kind).materialize(
                record, source, target
            )

    @staticmethod
    def _write_source_manifest(
        path: Path,
        records: tuple[ValidationImageRecord, ...],
    ) -> None:
        metadata_fields = tuple(
            sorted({name for record in records for name, _ in record.metadata})
        )
        fields = (
            "partition",
            "source_set_id",
            "well",
            "site",
            "channel",
            "relative_path",
            *metadata_fields,
        )
        with path.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=fields)
            writer.writeheader()
            for record in records:
                row = {
                    "partition": record.partition.value,
                    "source_set_id": record.source_set_id,
                    "well": record.well,
                    "site": record.site,
                    "channel": record.channel,
                    "relative_path": str(record.canonical_relative_path),
                }
                row.update(dict(record.metadata))
                writer.writerow(row)

    @staticmethod
    def _write_reference_manifest(
        path: Path,
        records: tuple[ValidationReferenceRecord, ...],
    ) -> None:
        with path.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(
                handle,
                fieldnames=(
                    "partition",
                    "source_set_id",
                    "channel",
                    "reference_kind",
                    "source_relative_path",
                    "relative_path",
                ),
            )
            writer.writeheader()
            for record in records:
                writer.writerow(
                    {
                        "partition": record.partition.value,
                        "source_set_id": record.source_set_id,
                        "channel": record.channel or "",
                        "reference_kind": record.reference_kind.value,
                        "source_relative_path": str(record.source_relative_path),
                        "relative_path": str(record.canonical_relative_path),
                    }
                )

    @staticmethod
    def _write_source_bindings(path: Path, config: SourceBindingsConfig) -> None:
        from pycodify import Assignment, generate_python_source

        import openhcs.serialization.pycodify_formatters  # noqa: F401

        path.write_text(
            generate_python_source(
                Assignment("source_bindings_config", config),
                header="# Derived OpenHCS source-binding declaration",
                clean_mode=True,
            ),
            encoding="utf-8",
        )

    @staticmethod
    def _write_pipeline_template(
        path: Path,
        config: SourceBindingsConfig,
    ) -> None:
        """Write a self-contained pipeline declaration for isolated runtimes."""

        from pycodify import Assignment, BlankLine, CodeBlock, generate_python_source

        import openhcs.serialization.pycodify_formatters  # noqa: F401

        lazy_config = LazySourceBindingsConfig(
            metadata_rules=config.metadata_rules,
            match_plan=config.match_plan,
            source_filters=config.source_filters,
            bindings=config.bindings,
            imported_metadata_tables=config.imported_metadata_tables,
            grouping_metadata_fields=config.grouping_metadata_fields,
        )
        pipeline_config = PipelineConfig(
            microscope=Microscope.SOURCE_BINDINGS,
            source_bindings_config=lazy_config,
        )
        path.write_text(
            generate_python_source(
                CodeBlock.from_items(
                    (
                        Assignment("pipeline_config", pipeline_config),
                        BlankLine(),
                        Assignment("pipeline_steps", []),
                    )
                ),
                header=(
                    "# Derived OpenHCS pipeline template; add typed FunctionStep "
                    "declarations below"
                ),
                clean_mode=True,
            ),
            encoding="utf-8",
        )

    @staticmethod
    def _write_authoring_guide(
        path: Path,
        spec: DatasetSpec,
        validation: IndependentValidationSpec,
        dsl_contract: ValidationDslContract,
    ) -> None:
        tracks = "\n".join(
            f"- `{track.name}` ({track.function_surface.value}): {track.objective} "
            f"Expected artifacts: {', '.join(track.expected_artifacts)}."
            for track in validation.authoring_tracks
        )
        transitions = "\n".join(
            f"- {transition}" for transition in dsl_contract.compiled_transitions
        )
        path.write_text(
            f"""# {spec.id} blind OpenHCS development surface

Use this directory as the complete filesystem mount for the authoring agent.
It contains declared development inputs and public metadata only. Held-out
inputs, manual references, accepted metric values, and the trusted scorer are
deliberately outside this tree.

## OpenHCS DSL contract

- Source components: {", ".join(dsl_contract.source_components)}
- Grouping metadata: `{", ".join(dsl_contract.grouping_fields)}`
- Variable components: {", ".join(dsl_contract.variable_components) or "none"}
- Source sets: {dsl_contract.source_set_count}
- Source planes: {dsl_contract.source_plane_count}
- Source-binding projection: inspect `source_bindings_config` in
  `source_bindings.py`; do not import it from the runnable pipeline.
- Runnable source: start from `pipeline_template.py`; it embeds the same derived
  source-binding declaration so compiler, UI and execution-server processes do
  not depend on a shared Python import working directory.
- Preserve typed artifacts and materialization declarations in the frozen pipeline.

The compiled dimensional transitions expected from the source declaration are:

{transitions}

## Authoring tracks

{tracks}

For a registered-custom track, add a typed function through OpenHCS registration
so its signature drives the UI, Python document, MCP schema, and compiler. Do not
inject code into a viewer or bypass the pipeline runtime.

Freeze the final pipeline before the held-out execution or trusted scoring
surface is mounted. Preserve every authoring attempt, compile refusal, generated
source file, materialized artifact, MCP event record, and multi-percentile
raw/result overlay.
""",
            encoding="utf-8",
        )


def source_bindings_for_validation(
    validation: IndependentValidationSpec,
) -> SourceBindingsConfig:
    """Derive OpenHCS source bindings from validation channel declarations."""

    aliases = tuple(channel.alias for channel in validation.channels)
    bindings = tuple(
        NamedSourceBinding(
            alias=channel.alias,
            selector=SourceSelector(
                metadata=(MetadataSelector(field="channel", value=channel.value),),
                inherit_current_scope=True,
            ),
            origin=SourceBindingOrigin.PIPELINE_START,
            component_identity=(
                ComponentSelector(
                    component=AllComponents.CHANNEL,
                    value=channel.value,
                ),
            ),
        )
        for channel in validation.channels
    )
    match_plan = None
    if len(bindings) > 1:
        match_plan = SourceBindingMatchPlan(
            method=SourceBindingMatchMethod.METADATA,
            dimensions=tuple(
                SourceBindingMatchDimension(
                    fields=tuple(
                        SourceBindingMatchField(
                            alias=alias,
                            metadata_field=metadata_field,
                        )
                        for alias in aliases
                    )
                )
                for metadata_field in validation.source_identity_fields
            ),
        )
    return SourceBindingsConfig(
        source_filters=(
            SourceFilterClause(
                subject=SourceFilterSubject.FILE,
                match_type=SourceFilterMatchType.IS_IMAGE,
            ),
        ),
        bindings=bindings,
        metadata_rules=(
            MetadataExtractionRule(
                source=MetadataSource.FILE_NAME,
                pattern=(
                    r"^(?:plate-(?P<plate>[^_]+)_)?"
                    r"well-(?P<well>[A-P]\d{2})_site-(?P<site>[^_]+)_"
                    r"channel-(?P<channel>[^.]+)\.(?:tif|tiff|bmp|png)$"
                ),
            ),
        ),
        match_plan=match_plan,
        imported_metadata_tables=(
            ImportedMetadataTable(
                location="source_manifest.csv",
                joins=tuple(
                    ImportedMetadataJoin(field, field)
                    for field in validation.source_identity_fields
                ),
            ),
        ),
        grouping_metadata_fields=validation.execution_group_fields,
    )


def derive_validation_dsl_contract(
    validation: IndependentValidationSpec,
    records: tuple[ValidationImageRecord, ...],
) -> ValidationDslContract:
    """Derive grouping and dimensional transitions from normalized records."""

    source_sets = {record.source_set_id for record in records}
    sites_by_group: dict[tuple[str, ...], set[str]] = {}
    for record in records:
        metadata = {
            "well": record.well,
            "site": record.site,
            "channel": record.channel,
            **dict(record.metadata),
        }
        group_identity = tuple(
            metadata[field] for field in validation.execution_group_fields
        )
        sites_by_group.setdefault(group_identity, set()).add(record.site)
    variable_components = tuple(
        component
        for component, is_variable in (
            ("site", any(len(sites) > 1 for sites in sites_by_group.values())),
        )
        if is_variable
    )
    source_components = (*validation.source_identity_fields, "channel")
    retained_components = ", ".join(validation.source_identity_fields)
    return ValidationDslContract(
        source_components=source_components,
        grouping_fields=validation.execution_group_fields,
        variable_components=variable_components,
        source_set_count=len(source_sets),
        source_plane_count=len(records),
        compiled_transitions=(
            (
                f"source planes {{{', '.join(source_components)}}} -> named channel "
                "bindings per source set"
            ),
            (
                "bound image arguments -> image/label artifacts retaining "
                f"{{{retained_components}}}"
            ),
            "label artifacts -> object tables keyed by source set and object label",
            "per-source artifacts -> declared materialization paths and plate summaries",
        ),
    )


def split_validation_records(
    validation: IndependentValidationSpec,
    records: tuple[ValidationImageRecord, ...],
) -> tuple[tuple[ValidationImageRecord, ...], tuple[ValidationImageRecord, ...]]:
    """Derive disjoint development and held-out planes from one owned split."""

    grouped_records: dict[str, list[ValidationImageRecord]] = {}
    for record in records:
        grouped_records.setdefault(record.source_set_id, []).append(record)
    grouped: dict[str, tuple[ValidationImageRecord, ...]] = {}
    for source_set_id, source_set_records in grouped_records.items():
        source_set = tuple(source_set_records)
        partitions = {record.partition for record in source_set}
        selection_keys = {record.selection_key for record in source_set}
        if len(partitions) != 1 or len(selection_keys) != 1:
            raise ValidationCorpusPreparationError(
                f"Validation source set {source_set_id!r} has inconsistent "
                "partition or selection identity."
            )
        grouped[source_set_id] = source_set

    development_ids = _selected_source_set_ids(
        grouped,
        validation.trial_split.development,
    )
    held_out_ids = _selected_source_set_ids(
        grouped,
        validation.trial_split.held_out,
        excluded=development_ids,
    )
    overlap = development_ids & held_out_ids
    if overlap:
        raise ValidationCorpusPreparationError(
            f"Development and held-out source sets overlap: {sorted(overlap)!r}."
        )
    if len(development_ids) != validation.trial_split.expected_development_source_sets:
        raise ValidationCorpusPreparationError(
            "Development split contains "
            f"{len(development_ids)} source sets; expected "
            f"{validation.trial_split.expected_development_source_sets}."
        )
    if len(held_out_ids) != validation.trial_split.expected_held_out_source_sets:
        raise ValidationCorpusPreparationError(
            f"Held-out split contains {len(held_out_ids)} source sets; expected "
            f"{validation.trial_split.expected_held_out_source_sets}."
        )
    development = tuple(
        record for record in records if record.source_set_id in development_ids
    )
    held_out = tuple(
        record for record in records if record.source_set_id in held_out_ids
    )
    return development, held_out


def _selected_source_set_ids(
    grouped: dict[str, tuple[ValidationImageRecord, ...]],
    selection: ValidationSourceSetSelection,
    *,
    excluded: frozenset[str] | set[str] = frozenset(),
) -> set[str]:
    candidates = tuple(
        (source_set_id, source_set[0])
        for source_set_id, source_set in grouped.items()
        if source_set_id not in excluded
        and source_set[0].partition in selection.partitions
    )
    if selection.include_selection_keys:
        requested = set(selection.include_selection_keys)
        candidates = tuple(
            candidate
            for candidate in candidates
            if candidate[1].selection_key in requested
        )
        found = {record.selection_key for _, record in candidates}
        missing = requested - found
        if missing:
            raise ValidationCorpusPreparationError(
                f"Declared validation selection keys are missing: {sorted(missing)!r}."
            )
    ordered = sorted(
        candidates,
        key=lambda candidate: (
            selection.order.key(candidate[1].selection_key, salt=selection.salt),
            candidate[0],
        ),
    )
    if selection.limit is not None:
        ordered = ordered[: selection.limit]
    return {source_set_id for source_set_id, _ in ordered}


def freeze_pipeline(
    dataset_id: str,
    pipeline_path: Path,
    *,
    corpus_root: Path,
) -> FrozenPipelineReceipt:
    """Record the exact pipeline bytes before trusted references are exposed."""

    pipeline_path = Path(pipeline_path).expanduser().resolve()
    if not pipeline_path.is_file():
        raise FileNotFoundError(f"Pipeline document does not exist: {pipeline_path}")
    dataset_root = Path(corpus_root).expanduser().resolve() / dataset_id
    if not dataset_root.is_dir():
        raise FileNotFoundError(f"Prepared dataset root does not exist: {dataset_root}")
    receipt = FrozenPipelineReceipt(
        dataset_id=dataset_id,
        pipeline_path=pipeline_path,
        pipeline_sha256=_sha256(pipeline_path),
        created_at_utc=datetime.now(UTC).isoformat(),
    )
    receipt_path = dataset_root / "frozen_pipeline_receipt.json"
    if receipt_path.exists():
        raise FileExistsError(
            f"Pipeline is already frozen for this corpus: {receipt_path}"
        )
    receipt_path.write_text(
        json.dumps(_json_value(receipt), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return receipt


def verify_frozen_pipeline(
    dataset_id: str,
    *,
    corpus_root: Path,
) -> FrozenPipelineReceipt:
    """Fail closed unless the current pipeline bytes match the freeze receipt."""

    receipt_path = (
        Path(corpus_root).expanduser().resolve()
        / dataset_id
        / "frozen_pipeline_receipt.json"
    )
    payload = json.loads(receipt_path.read_text(encoding="utf-8"))
    receipt = FrozenPipelineReceipt(
        dataset_id=payload["dataset_id"],
        pipeline_path=Path(payload["pipeline_path"]),
        pipeline_sha256=payload["pipeline_sha256"],
        created_at_utc=payload["created_at_utc"],
    )
    if receipt.dataset_id != dataset_id:
        raise ValidationCorpusPreparationError(
            f"Freeze receipt belongs to {receipt.dataset_id!r}, not {dataset_id!r}."
        )
    current_digest = _sha256(receipt.pipeline_path)
    if current_digest != receipt.pipeline_sha256:
        raise ValidationCorpusPreparationError(
            "Frozen pipeline bytes changed before scoring: "
            f"expected {receipt.pipeline_sha256}, found {current_digest}."
        )
    return receipt


def _hardlink_or_copy(source: Path, target: Path) -> None:
    if not source.is_file():
        raise FileNotFoundError(f"Declared validation source is missing: {source}")
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        raise FileExistsError(
            f"Normalized validation paths collide at {target}; source identity is incomplete."
        )
    try:
        os.link(source, target)
    except OSError:
        shutil.copy2(source, target)


def _verify_artifact(path: Path, expected_size: int, expected_sha256: str) -> None:
    actual_size = path.stat().st_size
    if actual_size != expected_size:
        raise ValidationCorpusPreparationError(
            f"Artifact {path} has {actual_size} bytes; expected {expected_size}."
        )
    actual_digest = _sha256(path)
    if actual_digest != expected_sha256:
        raise ValidationCorpusPreparationError(
            f"Artifact {path} has SHA-256 {actual_digest}; expected {expected_sha256}."
        )


def _verify_materialized_archive(archive_path: Path, raw_root: Path) -> None:
    """Verify every extracted member against the pinned archive's size and CRC."""

    with zipfile.ZipFile(archive_path) as archive:
        for member in archive.infolist():
            if member.is_dir():
                continue
            target = _safe_materialized_member(raw_root, member.filename)
            if not target.is_file():
                raise ValidationCorpusPreparationError(
                    f"Archive member was not materialized: {member.filename!r}."
                )
            if target.stat().st_size != member.file_size:
                raise ValidationCorpusPreparationError(
                    f"Materialized member size differs from {archive_path.name}: "
                    f"{member.filename!r}."
                )
            checksum = 0
            with target.open("rb") as handle:
                for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                    checksum = zlib.crc32(chunk, checksum)
            if checksum & 0xFFFFFFFF != member.CRC:
                raise ValidationCorpusPreparationError(
                    f"Materialized member CRC differs from {archive_path.name}: "
                    f"{member.filename!r}."
                )


def _safe_materialized_member(raw_root: Path, member_name: str) -> Path:
    target = (raw_root / member_name).resolve()
    root = raw_root.resolve()
    if target != root and root not in target.parents:
        raise ValidationCorpusPreparationError(
            f"Archive member escapes materialization root: {member_name!r}."
        )
    return target


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _partition_counts(
    records: tuple[ValidationImageRecord, ...],
) -> dict[str, int]:
    counts: dict[str, int] = {}
    for record in records:
        counts[record.partition.value] = counts.get(record.partition.value, 0) + 1
    return counts


def _json_value(value: Any) -> Any:
    if is_dataclass(value) and not isinstance(value, type):
        return {key: _json_value(item) for key, item in asdict(value).items()}
    if isinstance(value, Enum):
        return value.value
    if isinstance(value, Path):
        return str(value)
    if isinstance(value, dict):
        return {str(key): _json_value(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [_json_value(item) for item in value]
    return value
