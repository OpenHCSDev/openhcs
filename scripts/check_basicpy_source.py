"""Focused source-only BaSiCPy integration checks, without backend imports."""

from __future__ import annotations

import argparse
import ast
import tomllib
import unittest
from pathlib import Path

from packaging.requirements import Requirement

ROOT = Path(__file__).resolve().parents[1]
WRAPPER = ROOT / "openhcs/processing/backends/enhance/basic_processor_jax.py"


class BasicPySourceTests(unittest.TestCase):
    upstream_source: Path

    def setUp(self):
        self.tree = ast.parse(WRAPPER.read_text())
        self.function = next(
            node
            for node in self.tree.body
            if isinstance(node, ast.FunctionDef)
            and node.name == "basic_flatfield_correction_jax"
        )

    def test_reviewed_fork_is_an_ordinary_project_dependency(self):
        project = tomllib.loads((ROOT / "pyproject.toml").read_text())["project"]
        requirements = tuple(Requirement(value) for value in project["dependencies"])
        [fork] = [value for value in requirements if value.name == "openhcs-basicpy"]
        self.assertIsNone(fork.url)
        self.assertIn("1.3.0", fork.specifier)
        self.assertNotIn("2.0.0", fork.specifier)
        self.assertIsNotNone(fork.marker)
        for system, machine, admitted in (
            ("Linux", "x86_64", True),
            ("Windows", "AMD64", True),
            ("Darwin", "arm64", True),
            ("Darwin", "x86_64", False),
        ):
            with self.subTest(system=system, machine=machine):
                self.assertEqual(
                    fork.marker.evaluate(
                        {"platform_system": system, "platform_machine": machine}
                    ),
                    admitted,
                )

    def test_every_exposed_knob_reaches_real_model_owner(self):
        owner = next(
            node
            for node in ast.parse(self.upstream_source.read_text()).body
            if isinstance(node, ast.ClassDef) and node.name == "BaSiC"
        )
        fields = {
            node.target.id
            for node in owner.body
            if isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name)
        }
        call = next(
            node
            for node in ast.walk(self.function)
            if isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id == "BaSiC"
        )
        parameters = {arg.arg for arg in self.function.args.args[1:]}
        forwarded = {kw.arg for kw in call.keywords}
        self.assertEqual(parameters, forwarded)
        self.assertLessEqual(forwarded, fields)
        for keyword in call.keywords:
            self.assertEqual(ast.unparse(keyword.value), keyword.arg)

    def test_choices_belong_to_upstream_not_a_mirror(self):
        imports = {
            (node.module, alias.name)
            for node in self.tree.body
            if isinstance(node, ast.ImportFrom)
            for alias in node.names
        }
        self.assertIn(("basicpy.basicpy", "FittingMode"), imports)
        flatfield = ast.parse((WRAPPER.parent / "flatfield.py").read_text())
        self.assertFalse(
            any(
                isinstance(node, ast.ClassDef) and node.name == "BasicFittingMode"
                for node in flatfield.body
            )
        )

    def test_existing_contracts_own_pipeline_axis_admission(self):
        decorators = {ast.unparse(node) for node in self.function.decorator_list}
        self.assertIn(
            "jax_func(contract=ProcessingContract.PURE_3D, dtype_config_default=DtypeConfig())",
            decorators,
        )
        self.assertIn("allowed_group_by(GroupBy.CHANNEL)", decorators)
        self.assertIn(
            "required_variable_components(FittedIlluminationFieldOutput.observation_axis)",
            decorators,
        )
        self.assertFalse(
            any(
                isinstance(node, ast.FunctionDef) and "batch" in node.name
                for node in self.tree.body
            )
        )

    def test_float_output_and_dependency_failure_are_not_hidden(self):
        calls = [node for node in ast.walk(self.function) if isinstance(node, ast.Call)]
        self.assertFalse(
            any(
                isinstance(node.func, ast.Attribute)
                and node.func.attr in ("astype", "clip")
                for node in calls
            )
        )
        self.assertFalse(any(isinstance(node, ast.Try) for node in ast.walk(self.tree)))
        self.assertFalse(
            any(
                isinstance(node.func, ast.Name)
                and node.func.id == "optional_import_placeholder"
                for node in ast.walk(self.tree)
                if isinstance(node, ast.Call)
            )
        )
        transform = next(
            node
            for node in calls
            if isinstance(node.func, ast.Attribute)
            and node.func.attr == "fit_transform"
        )
        self.assertEqual(ast.unparse(transform.keywords[0].value), "False")

    def test_fields_extend_existing_projection_and_metadata_owners(self):
        tree = ast.parse((WRAPPER.parent / "flatfield.py").read_text())
        owner = next(
            node
            for node in tree.body
            if isinstance(node, ast.ClassDef)
            and node.name == "FittedIlluminationFieldOutput"
        )
        self.assertEqual(
            [ast.unparse(base) for base in owner.bases], ["SourceProjectedImageOutput"]
        )
        calls = [
            ast.unparse(node.func)
            for node in ast.walk(owner)
            if isinstance(node, ast.Call)
        ]
        self.assertIn(
            "image_payload_metadata(source).collapse_leading_plane_axis", calls
        )
        self.assertIn("image_payload_metadata(source).require_independent_observation_axis", calls)
        metadata_tree = ast.parse((ROOT / "openhcs/core/runtime_image_values.py").read_text())
        metadata_owner = next(
            node for node in metadata_tree.body
            if isinstance(node, ast.ClassDef) and node.name == "ImagePayloadMetadata"
        )
        metadata_calls = {
            ast.unparse(node.func) for node in ast.walk(metadata_owner)
            if isinstance(node, ast.Call)
        }
        declared_method_names = [
            node.name for node in metadata_owner.body
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        ]
        self.assertEqual(len(declared_method_names), len(set(declared_method_names)))
        self.assertIn("self.retained_plane_component_values", metadata_calls)
        self.assertFalse(any(call.endswith((".repeat", ".tile")) for call in calls))
        decorator = next(
            node
            for node in self.function.decorator_list
            if isinstance(node, ast.Call)
            and ast.unparse(node.func) == "artifact_outputs"
        )
        self.assertEqual(
            [ast.unparse(arg) for arg in decorator.args],
            ["CORRECTED_OUTPUT", "FLATFIELD_OUTPUT", "DARKFIELD_OUTPUT"],
        )

    def test_jax_owns_plugin_version_matching(self):
        project = tomllib.loads((ROOT / "pyproject.toml").read_text())["project"]
        for extra in ("gpu", "all"):
            jax_requirements = [
                dep
                for dep in project["optional-dependencies"][extra]
                if dep.startswith("jax")
            ]
            self.assertEqual(jax_requirements, ["jax[cuda12-local]>=0.9.2,<0.10"])

    def test_native_default_reaches_existing_arraybridge_owner(self):
        decorators = ast.parse(
            (ROOT / "external/arraybridge/src/arraybridge/decorators.py").read_text()
        )
        owner = next(
            node
            for node in decorators.body
            if isinstance(node, ast.FunctionDef)
            and node.name == "_create_memory_decorator"
        )
        declaration = next(
            node
            for node in ast.walk(owner)
            if isinstance(node, ast.FunctionDef) and node.name == "decorator"
        )
        self.assertIn(
            "dtype_config_default",
            {argument.arg for argument in declaration.args.kwonlyargs},
        )
        wrapper = next(
            node
            for node in decorators.body
            if isinstance(node, ast.FunctionDef)
            and node.name == "wrap_dtype_preserving_callable"
        )
        self.assertIn(
            "dtype_config_default",
            {argument.arg for argument in wrapper.args.kwonlyargs},
        )
        project = tomllib.loads((ROOT / "pyproject.toml").read_text())["project"]
        [arraybridge] = [
            Requirement(value)
            for value in project["dependencies"]
            if Requirement(value).name == "arraybridge"
        ]
        self.assertIsNone(arraybridge.url)
        self.assertIn("0.3.4", arraybridge.specifier)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--basicpy-source", type=Path, required=True)
    args = parser.parse_args()
    BasicPySourceTests.upstream_source = args.basicpy_source
    unittest.main(argv=[__file__], verbosity=2)
