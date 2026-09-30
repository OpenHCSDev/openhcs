"""Source-only issue257 probe: no OpenHCS imports, pixels, or runtime startup.

Execute the two implicated helper declarations and read the canonical owner's
regex from their ASTs. Extension substitution models filename construction;
this is not a whole-module, parser integration, or native execution test.
"""

from __future__ import annotations

import ast
from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path
import re
from typing import Callable


@dataclass(frozen=True)
class DeclarationProbe:
    extension_from_path: Callable[[str], str | None]
    qualify: Callable[[str, str | None], str]
    filename_pattern: re.Pattern[str]
    source_sha256: dict[str, str]

    @classmethod
    def load(cls, root: Path) -> DeclarationProbe:
        identity_path = root / "openhcs/core/steps/function_output_identity.py"
        projection_path = root / "openhcs/core/source_projection.py"
        identity_source = identity_path.read_bytes()
        projection_source = projection_path.read_bytes()
        identity_tree = ast.parse(identity_source, filename=str(identity_path))
        projection_tree = ast.parse(projection_source, filename=str(projection_path))
        extension_owner = next(
            node for node in identity_tree.body
            if isinstance(node, ast.ClassDef)
            and node.name == "FunctionOutputExtensionAuthority"
        )
        path_owner = next(
            node for node in identity_tree.body
            if isinstance(node, ast.ClassDef)
            and node.name == "FunctionOutputPathAuthority"
        )
        qualification = next(
            node for node in path_owner.body
            if isinstance(node, ast.FunctionDef)
            and node.name == "_qualified_filename"
        )
        module = ast.Module(
            body=[
                ast.ImportFrom(
                    module="__future__",
                    names=[ast.alias(name="annotations")],
                    level=0,
                ),
                extension_owner,
                qualification,
            ],
            type_ignores=[],
        )
        namespace = {"Path": Path}
        exec(compile(ast.fix_missing_locations(module), str(identity_path), "exec"), namespace)
        address_owner = next(
            node for node in projection_tree.body
            if isinstance(node, ast.ClassDef) and node.name == "OpenHCSPlaneAddress"
        )
        pattern_declaration = next(
            node.value for node in address_owner.body
            if isinstance(node, ast.AnnAssign)
            and isinstance(node.target, ast.Name)
            and node.target.id == "_filename_pattern"
        )
        if not isinstance(pattern_declaration, ast.Call):
            raise AssertionError("Canonical regex declaration changed; review this probe.")
        return cls(
            extension_from_path=namespace["FunctionOutputExtensionAuthority"].from_path,
            qualify=namespace["_qualified_filename"],
            filename_pattern=re.compile(ast.literal_eval(pattern_declaration.args[0])),
            source_sha256={
                str(identity_path.relative_to(root)): hashlib.sha256(identity_source).hexdigest(),
                str(projection_path.relative_to(root)): hashlib.sha256(projection_source).hexdigest(),
            },
        )

    def inspect(self, fixture: FilenameFixture) -> FilenameObservation:
        matched = self.filename_pattern.fullmatch(fixture.filename)
        if matched is None:
            raise AssertionError(f"Fixture is not canonical: {fixture.filename}")
        declared_extension = matched.group("extension")
        inferred_extension = self.extension_from_path(fixture.filename)
        if inferred_extension is None:
            raise AssertionError("Path extension unexpectedly absent.")
        # Model supplying the inferred extension to the canonical filename
        # constructor. All fixture coordinates remain unchanged.
        constructed = fixture.filename.removesuffix(declared_extension) + inferred_extension
        qualified = self.qualify(constructed, "centre_dots")
        qualified_with_correct_extension = self.qualify(fixture.filename, "centre_dots")
        observation = FilenameObservation(
            fixture=fixture.name,
            input_filename=fixture.filename,
            parser_declared_extension=declared_extension,
            path_inferred_extension=inferred_extension,
            modeled_constructed_filename=constructed,
            actual_qualified_filename=qualified,
            actual_qualified_canonical_filename=qualified_with_correct_extension,
            inferred_extension_matches_declaration=inferred_extension == declared_extension,
            qualified_address_parseable=self.filename_pattern.fullmatch(qualified) is not None,
            qualification_only_address_parseable=(
                self.filename_pattern.fullmatch(qualified_with_correct_extension) is not None
            ),
        )
        assert observation.inferred_extension_matches_declaration == fixture.expected_valid
        assert observation.qualified_address_parseable == fixture.expected_valid
        assert observation.qualification_only_address_parseable == fixture.expected_valid
        assert self.qualify(fixture.filename, None) == fixture.filename
        return observation


@dataclass(frozen=True)
class FilenameFixture:
    name: str
    filename: str
    expected_valid: bool


@dataclass(frozen=True)
class FilenameObservation:
    fixture: str
    input_filename: str
    parser_declared_extension: str
    path_inferred_extension: str
    modeled_constructed_filename: str
    actual_qualified_filename: str
    actual_qualified_canonical_filename: str
    inferred_extension_matches_declaration: bool
    qualified_address_parseable: bool
    qualification_only_address_parseable: bool


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    probe = DeclarationProbe.load(root)
    fixtures = (
        FilenameFixture("plain", "A01_s001_w1_z001_t001.tif", True),
        FilenameFixture("plain_compound_extension", "A01_s001_w1_z001_t001.ome.tif", True),
        FilenameFixture("dotted_well", "sample.v2_s001_w1_z001_t001.tif", False),
        FilenameFixture("ome_named_well", "image.ome.tif_s001_w1_z001_t001.tif", False),
        FilenameFixture("dotted_well_compound_extension", "sample.v2_s001_w1_z001_t001.ome.tif", False),
    )
    observations = tuple(probe.inspect(fixture) for fixture in fixtures)
    original_failure = (
        "image_centre_dots.ome.tif_s001_w1_z001_t001"
        ".ome.tif_s001_w1_z001_t001.tif"
    )
    assert observations[3].actual_qualified_filename == original_failure
    print(json.dumps({
        "scope": "source-declaration probe; construction modeled; no OpenHCS imports/native runtime",
        "source_sha256": probe.source_sha256,
        "matches_original_failed_basename": True,
        "observations": [asdict(observation) for observation in observations],
    }, indent=2))


if __name__ == "__main__":
    main()
