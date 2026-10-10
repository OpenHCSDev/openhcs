"""Shared declaration-owned path admission before and after source decoding."""

import ast
from pathlib import Path

import pytest
from polystore.virtual_workspace import SourcePixelRef

from openhcs.core.source_binding_workspace import SourceBindingWorkspaceProjector
from openhcs.core.source_bindings import (
    ComponentSelector,
    ImagePlaneSource,
    MetadataSelector,
    NamedSourceBinding,
    SourceBindingsConfig,
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
    SourceSelector,
)
from openhcs.core.source_projection import SourceCandidate
from openhcs.domains.microscopy.axes import Microscopy


def _candidate(path, *, identities=(), metadata=None):
    return SourceCandidate(
        source_ref=SourcePixelRef("disk", str(path)),
        relative_path=str(path),
        source_filter_paths=identities,
        metadata=metadata or {},
    )


@pytest.mark.parametrize("absolute_candidate", (False, True))
@pytest.mark.parametrize("explicit_uri", ("relative", "absolute", "file_uri"))
def test_exact_source_admission_agrees_before_and_after_decode(
    tmp_path, absolute_candidate, explicit_uri
):
    selected = tmp_path / "selected.czi"
    selected.touch()
    uris = {
        "relative": selected.name,
        "absolute": str(selected),
        "file_uri": selected.as_uri(),
    }
    binding = NamedSourceBinding(
        alias="selected", explicit_source=ImagePlaneSource(uri=uris[explicit_uri])
    )
    config = SourceBindingsConfig(bindings=(binding,))
    projector = SourceBindingWorkspaceProjector(config)
    for path, expected in ((selected, True), (tmp_path / "other.czi", False)):
        candidate = _candidate(path if absolute_candidate else path.name)
        assert config.discovery_path_matches(tmp_path, path) is expected
        assert (
            projector.candidate_matches_binding(candidate, binding, tmp_path)
            is expected
        )


@pytest.mark.parametrize(
    "relative_path, expected",
    (
        ("selected/a.czi", True),
        ("selected/b.czi", True),
        ("selected/c.czi", False),
        ("other/a.czi", False),
    ),
)
def test_binding_directory_regex_and_or_group_use_the_same_owner(
    tmp_path, relative_path, expected
):
    binding = NamedSourceBinding(
        alias="selected",
        selector=SourceSelector(
            filters=(
                SourceFilterClause(
                    SourceFilterSubject.DIRECTORY,
                    SourceFilterMatchType.CONTAINS_REGEX,
                    r"(?:^|/)selected$",
                ),
                SourceFilterClause(
                    SourceFilterSubject.FILE,
                    SourceFilterMatchType.EQUALS,
                    "a.czi",
                    any_group=0,
                ),
                SourceFilterClause(
                    SourceFilterSubject.FILE,
                    SourceFilterMatchType.EQUALS,
                    "b.czi",
                    any_group=0,
                ),
            )
        ),
    )
    config = SourceBindingsConfig(bindings=(binding,))
    candidate = _candidate(relative_path)
    assert config.discovery_path_matches(tmp_path, tmp_path / relative_path) is expected
    assert (
        SourceBindingWorkspaceProjector(config).candidate_matches_binding(
            candidate, binding, tmp_path
        )
        is expected
    )


@pytest.mark.parametrize(
    "metadata, expected",
    (
        ({"well": "A01", "channel": "1"}, True),
        ({"well": "B01", "channel": "1"}, False),
        ({"well": "A01", "channel": "2"}, False),
        ({}, False),
    ),
)
def test_physical_admission_does_not_predict_decoded_metadata_or_components(
    tmp_path, metadata, expected
):
    binding = NamedSourceBinding(
        alias="selected",
        selector=SourceSelector(
            metadata=(MetadataSelector("well", "A01"),),
            components=(ComponentSelector(Microscopy.Channel, "1"),),
        ),
    )
    config = SourceBindingsConfig(bindings=(binding,))
    assert config.discovery_path_matches(tmp_path, tmp_path / "unknown.czi")
    assert (
        SourceBindingWorkspaceProjector(config).candidate_matches_binding(
            _candidate("unknown.czi", metadata=metadata), binding, tmp_path
        )
        is expected
    )


def test_decoded_companion_filters_do_not_replace_exact_entrypoint_identity(tmp_path):
    entrypoint = tmp_path / "plate.fake"
    companion = tmp_path / "well-a01.tif"
    entrypoint.touch()
    companion.touch()
    selector = SourceSelector(
        filters=(
            SourceFilterClause(
                SourceFilterSubject.FILE,
                SourceFilterMatchType.EQUALS,
                companion.name,
            ),
        )
    )
    candidate = _candidate(
        entrypoint.name, identities=(entrypoint.name, companion.name)
    )
    for exact_source, expected in (
        (None, True),
        (entrypoint.name, True),
        (companion.name, False),
    ):
        binding = NamedSourceBinding(
            alias="selected",
            selector=selector,
            explicit_source=None
            if exact_source is None
            else ImagePlaneSource(uri=exact_source),
        )
        config = SourceBindingsConfig(bindings=(binding,))
        # Discovery cannot see companions; the adapter must keep compound readers.
        assert not config.discovery_path_matches(tmp_path, entrypoint)
        assert (
            SourceBindingWorkspaceProjector(config).candidate_matches_binding(
                candidate, binding, tmp_path
            )
            is expected
        )


def test_unrestricted_alias_keeps_union_without_erasing_other_alias_filters(tmp_path):
    selected = NamedSourceBinding(
        alias="selected",
        selector=SourceSelector(
            filters=(
                SourceFilterClause(
                    SourceFilterSubject.FILE,
                    SourceFilterMatchType.EQUALS,
                    "selected.czi",
                ),
            )
        ),
    )
    unrestricted = NamedSourceBinding(alias="all")
    config = SourceBindingsConfig(bindings=(selected, unrestricted))
    other = _candidate("other.czi")
    assert config.discovery_path_matches(tmp_path, tmp_path / other.relative_path)
    projector = SourceBindingWorkspaceProjector(config)
    assert not projector.candidate_matches_binding(other, selected, tmp_path)
    assert projector.candidate_matches_binding(other, unrestricted, tmp_path)


def test_preparation_consumers_cannot_reauthor_binding_or_java_lifetime():
    """Guard the two reviewed owner bypasses, without importing a Java runtime."""
    root = Path(__file__).resolve().parents[2]
    for path, class_name, method_name, owner_call, forbidden in (
        (
            "openhcs/core/source_bindings.py",
            "SourceBindingsConfig",
            "discovery_path_matches",
            "physical_path_matches",
            {"explicit_source", "selector"},
        ),
        (
            "openhcs/core/source_binding_workspace.py",
            "SourceBindingWorkspaceProjector",
            "candidate_matches_binding",
            "physical_path_matches",
            {"explicit_source", "filters"},
        ),
        (
            "openhcs/microscopes/bioformats_adapter.py",
            "BioFormatsJavaAdapter",
            "discover_stores",
            "is_single_file",
            {"ImageReader", "ensure_initialized", "isSingleFile"},
        ),
    ):
        tree = ast.parse((root / path).read_text())
        owner = next(
            node
            for node in tree.body
            if isinstance(node, ast.ClassDef) and node.name == class_name
        )
        method = next(
            node
            for node in owner.body
            if isinstance(node, ast.FunctionDef) and node.name == method_name
        )
        attributes = {
            node.attr for node in ast.walk(method) if isinstance(node, ast.Attribute)
        }
        assert owner_call in attributes, (path, method_name)
        assert not attributes & forbidden, (path, method_name, attributes & forbidden)
        if class_name == "BioFormatsJavaAdapter":
            assert not any(
                isinstance(node, ast.FunctionDef) and node.name == "_is_single_file"
                for node in owner.body
            )
