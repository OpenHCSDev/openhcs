"""Focused source-only BaSiCPy integration checks, without backend imports."""

from __future__ import annotations

import argparse
import ast
import re
import tomllib
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WRAPPER = ROOT / "openhcs/processing/backends/enhance/basic_processor_jax.py"


class BasicPySourceTests(unittest.TestCase):
    upstream_source: Path

    def setUp(self):
        self.tree = ast.parse(WRAPPER.read_text())
        self.function = next(
            node for node in self.tree.body
            if isinstance(node, ast.FunctionDef)
            and node.name == "basic_flatfield_correction_jax"
        )

    def test_every_exposed_knob_reaches_real_model_owner(self):
        owner = next(
            node for node in ast.parse(self.upstream_source.read_text()).body
            if isinstance(node, ast.ClassDef) and node.name == "BaSiC"
        )
        fields = {
            node.target.id for node in owner.body
            if isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name)
        }
        call = next(
            node for node in ast.walk(self.function)
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
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
            for node in self.tree.body if isinstance(node, ast.ImportFrom)
            for alias in node.names
        }
        self.assertIn(("basicpy.basicpy", "FittingMode"), imports)
        flatfield = ast.parse((WRAPPER.parent / "flatfield.py").read_text())
        self.assertFalse(any(
            isinstance(node, ast.ClassDef) and node.name == "BasicFittingMode"
            for node in flatfield.body
        ))

    def test_existing_contracts_own_pipeline_axis_admission(self):
        decorators = {ast.unparse(node) for node in self.function.decorator_list}
        self.assertIn("jax_func(contract=ProcessingContract.PURE_3D)", decorators)
        self.assertIn("allowed_group_by(GroupBy.CHANNEL)", decorators)
        self.assertIn("required_variable_components(VariableComponents.SITE)", decorators)
        self.assertFalse(any(
            isinstance(node, ast.FunctionDef) and "batch" in node.name
            for node in self.tree.body
        ))

    def test_float_output_and_dependency_failure_are_not_hidden(self):
        calls = [node for node in ast.walk(self.function) if isinstance(node, ast.Call)]
        self.assertFalse(any(
            isinstance(node.func, ast.Attribute) and node.func.attr in ("astype", "clip")
            for node in calls
        ))
        self.assertFalse(any(isinstance(node, ast.Try) for node in ast.walk(self.tree)))
        self.assertFalse(any(
            isinstance(node.func, ast.Name) and node.func.id == "optional_import_placeholder"
            for node in ast.walk(self.tree) if isinstance(node, ast.Call)
        ))
        transform = next(
            node for node in calls
            if isinstance(node.func, ast.Attribute) and node.func.attr == "fit_transform"
        )
        self.assertEqual(ast.unparse(transform.keywords[0].value), "False")

    def test_reviewed_git_pin_and_jax_owned_version_matching(self):
        requirement = next(
            line for line in (ROOT / "requirements-basicpy.txt").read_text().splitlines()
            if line and not line.startswith("#")
        )
        self.assertRegex(
            requirement,
            re.compile(r"^BaSiCPy @ git\+https://github.com/OpenHCSDev/BaSiCPy.git@[0-9a-f]{40}$"),
        )
        project = tomllib.loads((ROOT / "pyproject.toml").read_text())["project"]
        for extra in ("gpu", "all"):
            jax_requirements = [
                dep for dep in project["optional-dependencies"][extra]
                if dep.startswith("jax")
            ]
            self.assertEqual(jax_requirements, ["jax[cuda12-local]>=0.9.2,<0.10"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--basicpy-source", type=Path, required=True)
    args = parser.parse_args()
    BasicPySourceTests.upstream_source = args.basicpy_source
    unittest.main(argv=[__file__], verbosity=2)
