from polystore.virtual_workspace import SourcePixelRef

from openhcs.constants.constants import Backend
from openhcs.core.source_bindings import (
    ImagePlaneSource,
    MetadataExtractionRule,
    MetadataSource,
    MetadataSelector,
    NamedSourceBinding,
    SourceBindingMatchMethod,
    SourceBindingMatchPlan,
    SourceBindingOrigin,
    SourceBindingsConfig,
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
    SourceSelector,
    StepSourceBindingsConfig,
)
from openhcs.core.source_bindings_preview import (
    SourceBindingDiagnosticSeverity,
    SourceBindingsPreview,
    SourceInventory,
)


class FileManagerInventoryStub:
    """Minimal FileManagerLike implementation for VFS inventory tests."""

    def __init__(self, files: tuple[str, ...]) -> None:
        self.files = files
        self.calls: list[tuple[str, str, bool]] = []

    def list_files(
        self,
        directory: str,
        backend: str,
        *,
        recursive: bool = False,
    ) -> list[str]:
        self.calls.append((str(directory), backend, recursive))
        return list(self.files)


def test_source_bindings_preview_reuses_typed_filter_and_order_matching(tmp_path):
    source_root = tmp_path / "sources"
    source_root.mkdir()
    for name in (
        "A01_s1_DNA.tif",
        "A01_s1_GFP.tif",
        "A02_s1_DNA.tif",
        "A02_s1_GFP.tif",
        "notes.txt",
    ):
        (source_root / name).write_text("placeholder", encoding="utf-8")
    source_bindings = SourceBindingsConfig(
        source_filters=(
            SourceFilterClause(
                SourceFilterSubject.EXTENSION,
                SourceFilterMatchType.IS_TIF,
            ),
        ),
        bindings=(
            NamedSourceBinding(
                alias="DNA",
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            SourceFilterSubject.FILE,
                            SourceFilterMatchType.CONTAINS,
                            "DNA",
                        ),
                    ),
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
            ),
            NamedSourceBinding(
                alias="GFP",
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            SourceFilterSubject.FILE,
                            SourceFilterMatchType.CONTAINS,
                            "GFP",
                        ),
                    ),
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
            ),
        ),
        match_plan=SourceBindingMatchPlan(method=SourceBindingMatchMethod.ORDER),
    )
    inventory = SourceInventory.from_paths(
        tuple(sorted(source_root.iterdir())),
        source_root=source_root,
        source_backend=Backend.DISK,
        source_bindings=source_bindings,
    )

    preview = SourceBindingsPreview.from_config_and_step_bindings(
        source_bindings=source_bindings,
        step_bindings=StepSourceBindingsConfig(),
        inventory=inventory,
        sample_limit=1,
    )

    counts_by_alias = {
        row.alias: (row.matched_source_count, row.sample_paths)
        for row in preview.binding_rows
    }
    assert counts_by_alias["DNA"] == (2, ("A01_s1_DNA.tif",))
    assert counts_by_alias["GFP"] == (2, ("A01_s1_GFP.tif",))
    assert len(preview.source_set_rows) == 2
    assert preview.source_set_rows[0].paths_by_alias == (
        ("DNA", "A01_s1_DNA.tif"),
        ("GFP", "A01_s1_GFP.tif"),
    )


def test_source_inventory_uses_declared_image_plane_sources(tmp_path):
    source_root = tmp_path / "sources"
    source_root.mkdir()
    source_path = source_root / "A01_s1_DNA.tif"
    source_path.write_text("placeholder", encoding="utf-8")
    source_bindings = SourceBindingsConfig(
        image_plane_sources=(ImagePlaneSource(uri=str(source_path)),),
        metadata_rules=(
            MetadataExtractionRule(
                source=MetadataSource.FILE_NAME,
                pattern=r"(?P<well>A\d{2})_(?P<site>s\d+)_(?P<channel>DNA)\.tif",
            ),
        ),
        bindings=(
            NamedSourceBinding(
                alias="DNA",
                selector=SourceSelector(
                    metadata=(MetadataSelector("channel", "DNA"),),
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
            ),
        ),
    )

    inventory = SourceInventory.from_paths(
        (),
        source_root=source_root,
        source_backend=Backend.DISK,
        source_bindings=source_bindings,
    )
    preview = SourceBindingsPreview.from_config_and_step_bindings(
        source_bindings=source_bindings,
        step_bindings=StepSourceBindingsConfig(),
        inventory=inventory,
    )

    assert inventory.candidates[0].source_ref == SourcePixelRef(
        backend=Backend.DISK.value,
        backend_address=source_path.name,
    )
    assert inventory.candidates[0].relative_path == "A01_s1_DNA.tif"
    assert inventory.candidates[0].metadata["channel"] == "DNA"
    assert preview.binding_rows[0].matched_source_count == 1


def test_source_inventory_from_paths_applies_source_filters(tmp_path):
    source_root = tmp_path / "sources"
    source_root.mkdir()
    for name in ("A01_DNA.tif", "A01_GFP.tif", "notes.txt"):
        (source_root / name).write_text("placeholder", encoding="utf-8")
    source_bindings = SourceBindingsConfig(
        source_filters=(
            SourceFilterClause(
                SourceFilterSubject.EXTENSION,
                SourceFilterMatchType.IS_TIF,
            ),
            SourceFilterClause(
                SourceFilterSubject.FILE,
                SourceFilterMatchType.CONTAINS,
                "DNA",
            ),
        ),
    )

    inventory = SourceInventory.from_paths(
        tuple(sorted(source_root.iterdir())),
        source_root=source_root,
        source_backend=Backend.DISK,
        source_bindings=source_bindings,
    )

    assert tuple(candidate.relative_path for candidate in inventory.candidates) == (
        "A01_DNA.tif",
    )


def test_source_inventory_and_preview_use_resolved_step_override(tmp_path):
    source_root = tmp_path / "sources"
    source_root.mkdir()
    for name in ("A01_DNA.tif", "A01_GFP.tif"):
        (source_root / name).write_text("placeholder", encoding="utf-8")
    source_bindings = SourceBindingsConfig(
        bindings=(
            NamedSourceBinding(
                alias="DNA",
                origin=SourceBindingOrigin.PIPELINE_START,
            ),
        ),
    )
    step_bindings = StepSourceBindingsConfig(
        enabled=True,
        source_filters=(
            SourceFilterClause(
                SourceFilterSubject.FILE,
                SourceFilterMatchType.CONTAINS,
                "GFP",
            ),
        ),
        bindings=(
            NamedSourceBinding(
                alias="GFP",
                origin=SourceBindingOrigin.PIPELINE_START,
            ),
        ),
    )

    inventory = SourceInventory.from_paths(
        tuple(sorted(source_root.iterdir())),
        source_root=source_root,
        source_backend=Backend.DISK,
        source_bindings=source_bindings,
        step_bindings=step_bindings,
    )
    preview = SourceBindingsPreview.from_config_and_step_bindings(
        source_bindings=source_bindings,
        step_bindings=step_bindings,
        inventory=inventory,
    )

    assert tuple(candidate.relative_path for candidate in inventory.candidates) == (
        "A01_GFP.tif",
    )
    assert [(row.alias, row.declaration_scope) for row in preview.binding_rows] == [
        ("GFP", "step"),
    ]
    assert preview.binding_rows[0].matched_source_count == 1


def test_source_binding_preview_reports_required_alias_without_matches():
    source_bindings = SourceBindingsConfig(
        bindings=(
            NamedSourceBinding(
                alias="DNA",
                selector=SourceSelector(
                    filters=(
                        SourceFilterClause(
                            SourceFilterSubject.FILE,
                            SourceFilterMatchType.CONTAINS,
                            "DNA",
                        ),
                    ),
                ),
                origin=SourceBindingOrigin.PIPELINE_START,
            ),
        ),
    )

    preview = SourceBindingsPreview.from_config_and_step_bindings(
        source_bindings=source_bindings,
        step_bindings=StepSourceBindingsConfig(),
        inventory=SourceInventory(candidates=()),
    )

    assert preview.diagnostics[0].severity is SourceBindingDiagnosticSeverity.ERROR
    assert preview.diagnostics[0].code == "source_binding.no_match"
    assert preview.diagnostics[0].alias == "DNA"


def test_source_inventory_from_filemanager_uses_vfs_file_listing():
    filemanager = FileManagerInventoryStub(
        files=(
            "/vfs/plate/A01_DNA.tif",
            "/vfs/plate/A01_GFP.tif",
            "/vfs/plate/notes.txt",
        )
    )
    source_bindings = SourceBindingsConfig(
        source_filters=(
            SourceFilterClause(
                SourceFilterSubject.FILE,
                SourceFilterMatchType.CONTAINS,
                "DNA",
            ),
        ),
    )

    inventory = SourceInventory.from_filemanager(
        filemanager=filemanager,
        source_root="/vfs/plate",
        backend=Backend.ZARR.value,
        source_bindings=source_bindings,
    )

    assert filemanager.calls == [("/vfs/plate", "zarr", True)]
    assert tuple(candidate.relative_path for candidate in inventory.candidates) == (
        "A01_DNA.tif",
    )
