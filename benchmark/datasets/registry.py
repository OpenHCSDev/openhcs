"""Registry of benchmark datasets."""

from __future__ import annotations

from abc import ABC
from pathlib import Path
from typing import ClassVar

from metaclass_registry import AutoRegisterMeta

from benchmark.contracts.dataset import (
    ArchiveFormat,
    BenchmarkCategory,
    BenchmarkDatasetTag,
    CellProfilerBenchmarkCaseSpec,
    DatasetSourceKind,
    DatasetSourceSpec,
    DatasetSpec,
    DatasetValidationRule,
)
from benchmark.contracts.validation import (
    IndependentValidationSpec,
    PublishedAssayReference,
    ValidationArtifactKind,
    ValidationArtifactRole,
    ValidationArtifactSpec,
    ValidationAuthoringTrack,
    ValidationChannelSpec,
    ValidationDatasetLayout,
    ValidationEvidenceKind,
    ValidationFunctionSurface,
    ValidationMetricProfile,
    ValidationPartition,
    ValidationRepositorySource,
    ValidationSelectionOrder,
    ValidationSourceSetSelection,
    ValidationTrialSplit,
)
from openhcs.constants.constants import Microscope

CELLPROFILER_TUTORIALS_REPO = "https://github.com/CellProfiler/tutorials.git"
CELLPROFILER_TUTORIALS_REVISION = "264a8155da21a2d468051f78211bed2e580a8934"
CP4_BENCHMARK_SUPPLEMENT_REPO = (
    "https://github.com/carpenterlab/2021_Stirling_BMCBioInformatics.git"
)
CP4_BENCHMARK_SUPPLEMENT_REVISION = "40abc2e600fd46b74c213999dd25c5245048dc92"
CELL_ORIENTATION_REPO = "https://github.com/rgomez-AI/CellOrientation.git"
CHROMTRANS_REPO = "https://github.com/rgomez-AI/3DChromTrans.git"


BBBC039_INDEPENDENT_VALIDATION = IndependentValidationSpec(
    record_url="https://bbbc.broadinstitute.org/BBBC039",
    licence_name="CC0 1.0",
    licence_url="https://creativecommons.org/publicdomain/zero/1.0/",
    evidence_kind=ValidationEvidenceKind.INSTANCE_MASKS,
    layout=ValidationDatasetLayout.PARTITIONED_INSTANCE_MASKS,
    metric_profile=ValidationMetricProfile.INSTANCE_SEGMENTATION,
    artifacts=(
        ValidationArtifactSpec(
            name="images.zip",
            url="https://data.broadinstitute.org/bbbc/BBBC039/images.zip",
            sha256="6f30a5d4fe38c928ded972704f085975f8dc0d65d9aa366df00e5a9d449fddd7",
            size_bytes=77_915_748,
            kind=ValidationArtifactKind.ZIP_ARCHIVE,
            role=ValidationArtifactRole.INPUT,
        ),
        ValidationArtifactSpec(
            name="masks.zip",
            url="https://data.broadinstitute.org/bbbc/BBBC039/masks.zip",
            sha256="f9e6043d8ca56344a4886f96a700d804d6ee982f31e2b2cd3194af2a053c2710",
            size_bytes=2_753_811,
            kind=ValidationArtifactKind.ZIP_ARCHIVE,
            role=ValidationArtifactRole.REFERENCE,
        ),
        ValidationArtifactSpec(
            name="metadata.zip",
            url="https://data.broadinstitute.org/bbbc/BBBC039/metadata.zip",
            sha256="a2c1f900bed9ba92a99553efd4c2ae98598433691c7401d818653ab61110deb2",
            size_bytes=17_816,
            kind=ValidationArtifactKind.ZIP_ARCHIVE,
            role=ValidationArtifactRole.METADATA,
        ),
    ),
    channels=(ValidationChannelSpec(alias="dna", value="DNA"),),
    expected_input_planes=200,
    trial_split=ValidationTrialSplit(
        development=ValidationSourceSetSelection(
            partitions=(ValidationPartition.VALIDATION,),
            limit=4,
        ),
        held_out=ValidationSourceSetSelection(
            partitions=(ValidationPartition.TEST,),
        ),
        expected_development_source_sets=4,
        expected_held_out_source_sets=50,
    ),
    source_identity_fields=("plate", "well", "site"),
    execution_group_fields=("plate", "well"),
    reference_decoder_url=(
        "https://gist.github.com/jccaicedo/15e811722fca51e3ae90e8b43057f075"
    ),
    reference_decoder_revision="2dd780afdbde1d5410ed57030a011b2000cfc658",
    authoring_tracks=(
        ValidationAuthoringTrack(
            name="catalog_instance_segmentation",
            function_surface=ValidationFunctionSurface.CATALOG,
            objective=(
                "Author and visually debug a catalogue-only DNA instance-segmentation "
                "pipeline, then materialize one label image and object table per field."
            ),
            expected_artifacts=("instance_labels", "object_measurements"),
        ),
    ),
)


BBBC007_INDEPENDENT_VALIDATION = IndependentValidationSpec(
    record_url="https://bbbc.broadinstitute.org/BBBC007",
    licence_name="CC0 / rights waived",
    licence_url="https://creativecommons.org/publicdomain/zero/1.0/",
    evidence_kind=ValidationEvidenceKind.MANUAL_OUTLINES,
    layout=ValidationDatasetLayout.PAIRED_MANUAL_OUTLINES,
    metric_profile=ValidationMetricProfile.BOUNDARY_AND_INSTANCE,
    artifacts=(
        ValidationArtifactSpec(
            name="BBBC007_v1_images.zip",
            url="https://data.broadinstitute.org/bbbc/BBBC007/BBBC007_v1_images.zip",
            sha256="b7009e2fce0a3152a5c9adda916eaa699d09696f4bd02a7d05d12d041e30c6d1",
            size_bytes=6_435_776,
            kind=ValidationArtifactKind.ZIP_ARCHIVE,
            role=ValidationArtifactRole.INPUT,
        ),
        ValidationArtifactSpec(
            name="BBBC007_v1_outlines.zip",
            url="https://data.broadinstitute.org/bbbc/BBBC007/BBBC007_v1_outlines.zip",
            sha256="6a5246f9a9d743d22eafdb409fae638a8461af97e9ff9c4a92f25eba236224d3",
            size_bytes=652_531,
            kind=ValidationArtifactKind.ZIP_ARCHIVE,
            role=ValidationArtifactRole.REFERENCE,
        ),
    ),
    channels=(
        ValidationChannelSpec(alias="dna", value="DNA"),
        ValidationChannelSpec(alias="actin", value="ACTIN"),
    ),
    expected_input_planes=32,
    trial_split=ValidationTrialSplit(
        development=ValidationSourceSetSelection(
            partitions=(ValidationPartition.COMPLETE,),
            limit=4,
            order=ValidationSelectionOrder.SHA256,
            salt="slas-20260915",
        ),
        held_out=ValidationSourceSetSelection(
            partitions=(ValidationPartition.COMPLETE,),
        ),
        expected_development_source_sets=4,
        expected_held_out_source_sets=12,
    ),
    repository_sources=(
        ValidationRepositorySource(
            name="Haase sparse BBBC007 tutorial subset",
            url="https://github.com/haesleinhuepf/BioImageAnalysisNotebooks.git",
            revision="68845a1afaf53bf601958a3fa7d86f3cf8a43219",
            licence_name="BSD-3-Clause code / CC BY 4.0 book; BBBC007 data CC0",
            materialized_size_bytes=2_406_250,
            paths=(
                "docs/29_algorithm_validation/segmentation_quality_estimation.ipynb",
                "data/BBBC007_batch",
                "data/BBBC007_sparse_instance_annotation",
            ),
        ),
    ),
    authoring_tracks=(
        ValidationAuthoringTrack(
            name="catalog_seeded_cell_segmentation",
            function_surface=ValidationFunctionSurface.CATALOG,
            objective=(
                "Use paired DNA and actin bindings to segment nuclei and seeded cells "
                "with catalogue functions and materialize both label sets."
            ),
            expected_artifacts=("nucleus_labels", "cell_labels"),
        ),
        ValidationAuthoringTrack(
            name="typed_sparse_jaccard_extension",
            function_surface=ValidationFunctionSurface.REGISTERED_CUSTOM,
            objective=(
                "Register a typed sparse-reference comparison function, expose it through "
                "the same reflected UI/MCP catalogue, and materialize its metric table."
            ),
            expected_artifacts=("sparse_metric_table",),
        ),
    ),
)


BBBC013_INDEPENDENT_VALIDATION = IndependentValidationSpec(
    record_url="https://bbbc.broadinstitute.org/BBBC013",
    licence_name="CC BY 3.0",
    licence_url="https://creativecommons.org/licenses/by/3.0/",
    evidence_kind=ValidationEvidenceKind.PLATE_BIOLOGY,
    layout=ValidationDatasetLayout.TRANSLOCATION_PLATE,
    metric_profile=ValidationMetricProfile.TRANSLOCATION_ASSAY,
    artifacts=(
        ValidationArtifactSpec(
            name="BBBC013_v1_images_bmp.zip",
            url="https://data.broadinstitute.org/bbbc/BBBC013/BBBC013_v1_images_bmp.zip",
            sha256="c059b569d96f70ad5626fad144867e6ece4353622119c46a8af8f9794f1e7985",
            size_bytes=32_404_692,
            kind=ValidationArtifactKind.ZIP_ARCHIVE,
            role=ValidationArtifactRole.INPUT,
        ),
        ValidationArtifactSpec(
            name="BBBC013_reproduce_logan.zip",
            url="https://data.broadinstitute.org/bbbc/BBBC013/BBBC013_reproduce_logan.zip",
            sha256="5ab59bbaddf75fee08436d2d7cfc7460ebfdaa6fdf1b8adb71274c7c27f885f3",
            size_bytes=5_557_596,
            kind=ValidationArtifactKind.ZIP_ARCHIVE,
            role=ValidationArtifactRole.REPRODUCTION,
        ),
        ValidationArtifactSpec(
            name="BBBC013_v1_platemap_all.txt",
            url="https://data.broadinstitute.org/bbbc/BBBC013/BBBC013_v1_platemap_all.txt",
            sha256="e8db6666271d47962fa7d2abfa3ea965352b8e87bee461f2983d0f667bc7ff08",
            size_bytes=513,
            kind=ValidationArtifactKind.FILE,
            role=ValidationArtifactRole.METADATA,
        ),
        ValidationArtifactSpec(
            name="BBBC013_v1_platemap_wortmannin.txt",
            url="https://data.broadinstitute.org/bbbc/BBBC013/BBBC013_v1_platemap_wortmannin.txt",
            sha256="c833784cb9f797562c07b3c5d21b03739fb88436ff31847d408528aebf00f59b",
            size_bytes=318,
            kind=ValidationArtifactKind.FILE,
            role=ValidationArtifactRole.METADATA,
        ),
        ValidationArtifactSpec(
            name="BBBC013_v1_platemap_ly294002.txt",
            url="https://data.broadinstitute.org/bbbc/BBBC013/BBBC013_v1_platemap_ly294002.txt",
            sha256="1dcdee3cd49ab7c5b4f6fc9fbe3e10034df3aa3cbae6c83c25a5b457aabf6834",
            size_bytes=279,
            kind=ValidationArtifactKind.FILE,
            role=ValidationArtifactRole.METADATA,
        ),
    ),
    channels=(
        ValidationChannelSpec(alias="gfp", value="GFP"),
        ValidationChannelSpec(alias="dna", value="DNA"),
    ),
    expected_input_planes=192,
    trial_split=ValidationTrialSplit(
        development=ValidationSourceSetSelection(
            partitions=(ValidationPartition.COMPLETE,),
            include_selection_keys=("A04", "B08", "E04", "F08"),
        ),
        held_out=ValidationSourceSetSelection(
            partitions=(ValidationPartition.COMPLETE,),
        ),
        expected_development_source_sets=4,
        expected_held_out_source_sets=92,
    ),
    published_assay_references=(
        PublishedAssayReference(
            name="carpenter_2006_z_prime_both_drugs",
            value=0.91,
            citation_url="https://doi.org/10.1186/gb-2006-7-10-r100",
        ),
        PublishedAssayReference(
            name="carpenter_2006_v_factor_wortmannin",
            value=0.86,
            citation_url="https://doi.org/10.1186/gb-2006-7-10-r100",
        ),
        PublishedAssayReference(
            name="carpenter_2006_v_factor_ly294002",
            value=0.84,
            citation_url="https://doi.org/10.1186/gb-2006-7-10-r100",
        ),
        PublishedAssayReference(
            name="logan_2010_z_prime_wortmannin",
            value=0.94,
            citation_url="https://doi.org/10.1177/1087057110370895",
        ),
        PublishedAssayReference(
            name="logan_2010_z_prime_ly294002",
            value=0.90,
            citation_url="https://doi.org/10.1177/1087057110370895",
        ),
        PublishedAssayReference(
            name="logan_2010_v_factor_wortmannin",
            value=0.86,
            citation_url="https://doi.org/10.1177/1087057110370895",
        ),
        PublishedAssayReference(
            name="logan_2010_v_factor_ly294002",
            value=0.88,
            citation_url="https://doi.org/10.1177/1087057110370895",
        ),
    ),
    authoring_tracks=(
        ValidationAuthoringTrack(
            name="catalog_translocation_measurement",
            function_surface=ValidationFunctionSurface.CATALOG,
            objective=(
                "Segment nuclei/cells from paired DNA and GFP planes, measure nuclear "
                "versus cytoplasmic GFP, and materialize per-cell and per-well tables."
            ),
            expected_artifacts=(
                "nucleus_labels",
                "cell_labels",
                "cell_table",
                "well_table",
            ),
        ),
        ValidationAuthoringTrack(
            name="typed_plate_statistics_extension",
            function_surface=ValidationFunctionSurface.REGISTERED_CUSTOM,
            objective=(
                "Register a typed plate-statistics function over the per-well table and "
                "materialize dose-response, Z-prime and replicate-SD V-factor outputs."
            ),
            expected_artifacts=("assay_statistics", "dose_response_table"),
        ),
    ),
)


class BenchmarkDatasetDeclaration(ABC, metaclass=AutoRegisterMeta):
    """Registered declaration for one benchmark dataset."""

    __registry__: ClassVar[dict[str, type["BenchmarkDatasetDeclaration"]]] = {}
    __registry_key__ = "id"
    __skip_if_no_key__ = True

    id: ClassVar[str | None] = None
    public_alias: ClassVar[str | None] = None
    urls: ClassVar[tuple[str, ...]] = ()
    size_bytes: ClassVar[int]
    archive_format: ClassVar[ArchiveFormat] = ArchiveFormat.ZIP
    microscope_type: ClassVar[str]
    validation_rule: ClassVar[DatasetValidationRule] = DatasetValidationRule.NON_EMPTY
    reference_cppipe_urls: ClassVar[tuple[str, ...]] = ()
    expected_count: ClassVar[int | None] = None
    manifest_path: ClassVar[Path | None] = None
    source: ClassVar[DatasetSourceSpec | None] = None
    benchmark_cases: ClassVar[tuple[CellProfilerBenchmarkCaseSpec, ...]] = ()
    tags: ClassVar[frozenset[BenchmarkDatasetTag]] = frozenset()
    independent_validation: ClassVar[IndependentValidationSpec | None] = None

    @classmethod
    def to_spec(cls) -> DatasetSpec:
        """Materialize this declaration as a public dataset spec."""
        if cls.id is None:
            raise ValueError(f"{cls.__name__} must declare a dataset id.")
        return DatasetSpec(
            id=cls.id,
            urls=list(cls.urls),
            size_bytes=cls.size_bytes,
            archive_format=cls.archive_format,
            microscope_type=cls.microscope_type,
            validation_rule=cls.validation_rule,
            reference_cppipe_urls=cls.reference_cppipe_urls,
            expected_count=cls.expected_count,
            manifest_path=cls.manifest_path,
            source=cls.source,
            benchmark_cases=cls.benchmark_cases,
            tags=cls.tags,
            independent_validation=cls.independent_validation,
        )


class SourceBindingsDatasetMixin:
    """Declare ordinary image files whose ingestion comes from source bindings."""

    microscope_type: ClassVar[str] = Microscope.SOURCE_BINDINGS.value


class ImageCountValidatedDatasetMixin:
    """Dataset declaration mixin for image-count validated datasets."""

    validation_rule: ClassVar[DatasetValidationRule] = DatasetValidationRule.IMAGE_COUNT
    expected_count: ClassVar[int]


def _case(
    name: str,
    cppipe_path: str,
    dataset_path: str,
    *,
    assay_category: str,
    module_category: str,
    dataset_id: str | None = None,
    value_only: bool = True,
    timeout_seconds: float | None = 900.0,
) -> CellProfilerBenchmarkCaseSpec:
    """Declare one dataset-relative CellProfiler benchmark case."""
    return CellProfilerBenchmarkCaseSpec(
        name=name,
        cppipe_path=Path(cppipe_path),
        dataset_path=Path(dataset_path),
        dataset_id=dataset_id,
        category=BenchmarkCategory(assay=assay_category, module=module_category),
        value_only=value_only,
        cellprofiler_timeout_seconds=timeout_seconds,
    )


def _git_sparse(
    git_url: str,
    *sparse_paths: str,
    git_ref: str = "HEAD",
) -> DatasetSourceSpec:
    """Declare a sparse git acquisition source."""
    return DatasetSourceSpec(
        kind=DatasetSourceKind.GIT_SPARSE,
        git_url=git_url,
        git_ref=git_ref,
        sparse_paths=tuple(sparse_paths),
    )


def _git_sparse_with_archives(
    git_url: str,
    urls: tuple[str, ...],
    *sparse_paths: str,
    git_ref: str = "HEAD",
    tls_verify: bool = True,
) -> DatasetSourceSpec:
    """Declare a sparse git acquisition source with companion data archives."""
    return DatasetSourceSpec(
        kind=DatasetSourceKind.GIT_SPARSE_WITH_ARCHIVES,
        urls=urls,
        git_url=git_url,
        git_ref=git_ref,
        sparse_paths=tuple(sparse_paths),
        tls_verify=tls_verify,
    )


class Bbbc021Week122123Dataset(
    ImageCountValidatedDatasetMixin,
    SourceBindingsDatasetMixin,
    BenchmarkDatasetDeclaration,
):
    """Dataset declaration for BBBC021_Week1_22123."""

    id = "BBBC021_Week1_22123"
    public_alias = "BBBC021_SINGLE_PLATE"
    urls = (
        "https://data.broadinstitute.org/bbbc/BBBC021/BBBC021_v1_images_Week1_22123.zip",
    )
    size_bytes = 839000000
    reference_cppipe_urls = (
        "https://data.broadinstitute.org/bbbc/BBBC021/analysis.cppipe",
        "https://data.broadinstitute.org/bbbc/BBBC021/illum.cppipe",
    )
    expected_count = 720


class Bbbc02220585W1Dataset(
    ImageCountValidatedDatasetMixin,
    SourceBindingsDatasetMixin,
    BenchmarkDatasetDeclaration,
):
    """Dataset declaration for BBBC022_20585_w1."""

    id = "BBBC022_20585_w1"
    public_alias = "BBBC022_SINGLE_PLATE_DNA"
    urls = ("http://www.broadinstitute.org/bbbc/BBBC022/BBBC022_v1_images_20585w1.zip",)
    size_bytes = 7800000000
    expected_count = 3456


class Bbbc010WormsDataset(SourceBindingsDatasetMixin, BenchmarkDatasetDeclaration):
    """Dataset declaration for BBBC010_worms."""

    id = "BBBC010_worms"
    public_alias = "BBBC010_WORMS"
    urls = (
        "https://data.broadinstitute.org/bbbc/BBBC010/BBBC010_v2_images.zip",
        "https://data.broadinstitute.org/bbbc/BBBC010/BBBC010_v1_foreground.zip",
        "https://data.broadinstitute.org/bbbc/BBBC010/BBBC010_v1_foreground_eachworm.zip",
    )
    size_bytes = 72222003


class Bbbc011WormsMetabolismDataset(
    SourceBindingsDatasetMixin,
    BenchmarkDatasetDeclaration,
):
    """Dataset declaration for BBBC011_worms_metabolism."""

    id = "BBBC011_worms_metabolism"
    public_alias = "BBBC011_WORMS_METABOLISM"
    urls = ("https://data.broadinstitute.org/bbbc/BBBC011/BBBC011_v1_images.zip",)
    size_bytes = 39876190


class Bbbc012WormsInfectionMarkerDataset(
    SourceBindingsDatasetMixin,
    BenchmarkDatasetDeclaration,
):
    """Dataset declaration for BBBC012_worms_infection_marker."""

    id = "BBBC012_worms_infection_marker"
    public_alias = "BBBC012_WORMS_INFECTION_MARKER"
    urls = ("https://data.broadinstitute.org/bbbc/BBBC012/BBBC012_v1_images.zip",)
    size_bytes = 122677100


class Bbbc013U2osTranslocationDataset(
    SourceBindingsDatasetMixin,
    BenchmarkDatasetDeclaration,
):
    """Dataset declaration for BBBC013_u2os_translocation_bmp."""

    id = "BBBC013_u2os_translocation_bmp"
    public_alias = "BBBC013_U2OS_TRANSLOCATION"
    independent_validation = BBBC013_INDEPENDENT_VALIDATION
    urls = tuple(
        artifact.url
        for artifact in independent_validation.artifacts
        if artifact.kind is ValidationArtifactKind.ZIP_ARCHIVE
    )
    size_bytes = independent_validation.archive_size_bytes
    reference_cppipe_urls = tuple(
        artifact.url
        for artifact in independent_validation.artifacts_for(
            ValidationArtifactRole.REPRODUCTION
        )
    )


class Bbbc007CellBoundaryDataset(
    ImageCountValidatedDatasetMixin,
    SourceBindingsDatasetMixin,
    BenchmarkDatasetDeclaration,
):
    """Dataset declaration for BBBC007 manual nucleus/cell outlines."""

    id = "BBBC007_cell_boundaries"
    public_alias = "BBBC007_CELL_BOUNDARIES"
    independent_validation = BBBC007_INDEPENDENT_VALIDATION
    urls = tuple(
        artifact.url
        for artifact in independent_validation.artifacts
        if artifact.kind is ValidationArtifactKind.ZIP_ARCHIVE
    )
    size_bytes = independent_validation.archive_size_bytes
    expected_count = 64


class Bbbc038FullDataset(
    ImageCountValidatedDatasetMixin,
    SourceBindingsDatasetMixin,
    BenchmarkDatasetDeclaration,
):
    """Dataset declaration for BBBC038_full."""

    id = "BBBC038_full"
    public_alias = "BBBC038_FULL"
    urls = (
        "https://data.broadinstitute.org/bbbc/BBBC038/stage1_train.zip",
        "https://data.broadinstitute.org/bbbc/BBBC038/stage1_test.zip",
        "https://data.broadinstitute.org/bbbc/BBBC038/stage2_test_final.zip",
    )
    size_bytes = 382000000
    expected_count = 33215


class Bbbc039NucleiSegmentationDataset(
    ImageCountValidatedDatasetMixin,
    SourceBindingsDatasetMixin,
    BenchmarkDatasetDeclaration,
):
    """Dataset declaration for BBBC039_nuclei_segmentation."""

    id = "BBBC039_nuclei_segmentation"
    public_alias = "BBBC039_NUCLEI_SEGMENTATION"
    independent_validation = BBBC039_INDEPENDENT_VALIDATION
    urls = tuple(
        artifact.url
        for artifact in independent_validation.artifacts
        if artifact.kind is ValidationArtifactKind.ZIP_ARCHIVE
    )
    size_bytes = independent_validation.archive_size_bytes
    expected_count = 800


class Singh2014IlluminationCorrectionDataset(
    SourceBindingsDatasetMixin, BenchmarkDatasetDeclaration
):
    """Dataset declaration for Singh_2014_illumination_correction."""

    id = "Singh_2014_illumination_correction"
    public_alias = "SINGH_2014_ILLUMINATION_CORRECTION"
    urls = (
        "https://cellprofiler-published-pipelines.s3.amazonaws.com/JMicroscopy_Singh_2014.zip",
    )
    size_bytes = 30619586


class Sanz2019HistologyDataset(SourceBindingsDatasetMixin, BenchmarkDatasetDeclaration):
    """Dataset declaration for Sanz_2019_histology."""

    id = "Sanz_2019_histology"
    public_alias = "SANZ_2019_HISTOLOGY"
    urls = (
        "https://cellprofiler-published-pipelines.s3.amazonaws.com/Sanz_JAP_2019.zip",
    )
    size_bytes = 4541253


class Tian2019NeuronsDataset(SourceBindingsDatasetMixin, BenchmarkDatasetDeclaration):
    """Dataset declaration for Tian_2019_neurons."""

    id = "Tian_2019_neurons"
    public_alias = "TIAN_2019_NEURONS"
    urls = (
        "https://cellprofiler-published-pipelines.s3.amazonaws.com/Tian_Neuron_2019.zip",
    )
    size_bytes = 52207


class Sokolov2023NeuronsDataset(
    SourceBindingsDatasetMixin, BenchmarkDatasetDeclaration
):
    """Dataset declaration for Sokolov_2023_neurons."""

    id = "Sokolov_2023_neurons"
    public_alias = "SOKOLOV_2023_NEURONS"
    urls = (
        "https://cellprofiler-published-pipelines.s3.amazonaws.com/AM+Sokolov+Cell+Morphology+pipeline.zip",
    )
    size_bytes = 3403


class CellOrientationWoundHealingDataset(
    SourceBindingsDatasetMixin, BenchmarkDatasetDeclaration
):
    """Dataset declaration for CellOrientation_wound_healing."""

    id = "CellOrientation_wound_healing"
    public_alias = "CELL_ORIENTATION_WOUND_HEALING"
    size_bytes = 201274355
    source = _git_sparse_with_archives(
        CELL_ORIENTATION_REPO,
        ("https://public-docs.crg.es/almu/rgomez/Jennifer_Jungfleisch/Dataset.zip",),
        "workflow",
        tls_verify=False,
    )


class ChromTrans3dFishDataset(SourceBindingsDatasetMixin, BenchmarkDatasetDeclaration):
    """Dataset declaration for ChromTrans_3d_fish."""

    id = "ChromTrans_3d_fish"
    public_alias = "CHROMTRANS_3D_FISH"
    size_bytes = 98822670
    source = _git_sparse_with_archives(
        CHROMTRANS_REPO,
        ("https://public-docs.crg.es/almu/rgomez/Anna_Oncins/Dataset.zip",),
        "workflow",
        tls_verify=False,
    )


class CellProfilerTutorialsDataset(
    SourceBindingsDatasetMixin,
    BenchmarkDatasetDeclaration,
):
    """Dataset declaration for CellProfiler_tutorials."""

    id = "CellProfiler_tutorials"
    public_alias = "CELLPROFILER_TUTORIALS"
    size_bytes = 650000000
    source = _git_sparse(
        CELLPROFILER_TUTORIALS_REPO,
        "3DNoiseNuclei",
        "3d_monolayer",
        "AdvancedSegmentation",
        "BeginnerSegmentation",
        "PixelBasedClassification",
        "QualityControl",
        "Translocation",
        git_ref=CELLPROFILER_TUTORIALS_REVISION,
    )
    benchmark_cases = (
        _case(
            "cp_tutorial_3d_noise_nuclei",
            "3DNoiseNuclei/3DNucleiPipelineComputeConsumingFinal.cppipe",
            "3DNoiseNuclei/Input3DNuclei",
            assay_category="3D nuclei segmentation",
            module_category="3D segmentation",
            timeout_seconds=None,
        ),
        _case(
            "cp_tutorial_3d_monolayer",
            "3d_monolayer/3d_monolayer_final.cppipe",
            "3d_monolayer/images",
            assay_category="3D monolayer morphology",
            module_category="3D segmentation + measurement",
        ),
        _case(
            "cp_tutorial_advanced_segmentation_final",
            "AdvancedSegmentation/BBBC022_Analysis_Final.cppipe",
            "AdvancedSegmentation/BBBC022_20585_AE",
            assay_category="Cell Painting morphology",
            module_category="Advanced segmentation + measurement",
        ),
        _case(
            "cp_tutorial_quality_control",
            "QualityControl/BBBC022_QC.cppipe",
            "QualityControl/BBBC022_20585_AE",
            assay_category="Cell Painting quality control",
            module_category="Image quality measurement",
        ),
        _case(
            "cp_tutorial_beginner_segmentation_final",
            "BeginnerSegmentation/segmentation_final.cppipe",
            "BeginnerSegmentation/images_Illum-corrected",
            assay_category="Cell morphology",
            module_category="Segmentation + intensity measurement",
        ),
        _case(
            "cp_tutorial_pixel_based_classification",
            "PixelBasedClassification/pixel_based_classification_cho.cppipe",
            "PixelBasedClassification/images",
            assay_category="Pixel classification",
            module_category="Pixel classification",
        ),
        _case(
            "cp_tutorial_translocation_final",
            "Translocation/Translocation_final.cppipe",
            "Translocation/TranslocationData",
            assay_category="Translocation assay",
            module_category="Segmentation + classification",
        ),
    )


class CellProfiler4BenchmarkSupplementDataset(
    SourceBindingsDatasetMixin,
    BenchmarkDatasetDeclaration,
):
    """Dataset declaration for CellProfiler4_benchmark_supplement."""

    id = "CellProfiler4_benchmark_supplement"
    public_alias = "CELLPROFILER4_BENCHMARK_SUPPLEMENT"
    size_bytes = 5000000
    source = _git_sparse(
        CP4_BENCHMARK_SUPPLEMENT_REPO,
        "CombineObjects",
        git_ref=CP4_BENCHMARK_SUPPLEMENT_REVISION,
    )
    benchmark_cases = (
        _case(
            "cp4_supplement_combine_objects",
            "CombineObjects/CombineObjectsDemo.cppipe",
            "CombineObjects",
            assay_category="Object-combination benchmark",
            module_category="Object set algebra",
        ),
    )


from benchmark.datasets import (
    bioformats_hcs as _bioformats_hcs_declarations,
)  # noqa: E402,F401


def dataset_declarations() -> tuple[type[BenchmarkDatasetDeclaration], ...]:
    """Return registered benchmark dataset declarations."""
    return tuple(BenchmarkDatasetDeclaration.__registry__.values())


def dataset_specs() -> tuple[DatasetSpec, ...]:
    """Return materialized benchmark dataset specs."""
    return tuple(declaration.to_spec() for declaration in dataset_declarations())


DATASET_REGISTRY: dict[str, DatasetSpec] = {spec.id: spec for spec in dataset_specs()}


def _dataset_public_aliases() -> dict[str, DatasetSpec]:
    aliases: dict[str, DatasetSpec] = {}
    for declaration in dataset_declarations():
        dataset_id = declaration.id
        public_alias = declaration.public_alias
        if dataset_id is not None and public_alias is not None:
            aliases[public_alias] = DATASET_REGISTRY[dataset_id]
    return aliases


globals().update(_dataset_public_aliases())


def get_dataset_spec(dataset_id: str) -> DatasetSpec:
    """
    Retrieve a dataset specification by id.

    Raises:
        KeyError: if dataset id is unknown.
    """
    try:
        return DATASET_REGISTRY[dataset_id]
    except KeyError as exc:
        raise KeyError(
            f"Unknown dataset id '{dataset_id}'. "
            f"Available: {list(DATASET_REGISTRY.keys())}"
        ) from exc
