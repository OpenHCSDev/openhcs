"""A CellProfiler pipeline imports even when a module cannot run here.

Two cases: the module has no OpenHCS declaration, or it has one but the
distribution its file requires is not installed. Both import into ordinary
steps and are refused at compile time with a message saying what to do.
"""

from __future__ import annotations

import importlib
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest
from objectstate.lazy_factory import ensure_global_config_context
from objectstate.object_state import ObjectState
from objectstate.object_state_registry import ObjectStateRegistry
from packaging.requirements import Requirement

from benchmark.converter.cppipe_corpus import in_tree_cppipe_corpus
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
from openhcs.core.function_patterns import normalize_function_pattern
from openhcs.core.function_step_transport import FunctionStepTransportAuthority
from openhcs.core.invocation_artifacts import (
    PipelineInvocationContractProviderAuthority,
)
from openhcs.core.pipeline.compilation_session import (
    CompilationSession,
    ResolvedPipelineDefinition,
)
from openhcs.core.pipeline.funcstep_contract_validator import (
    FuncStepContractValidator,
)
from openhcs.core.steps.function_step import FunctionStep
from openhcs.interop.cellprofiler import pipeline_import
from openhcs.interop.cellprofiler.module_artifact_contracts import (
    UnknownArtifactInput,
)
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.interop.cellprofiler.parser import CPPipeParser
from openhcs.interop.cellprofiler.pipeline_import import import_cellprofiler_pipeline
from openhcs.processing.backends.cellprofiler.undeclared_module import (
    UndeclaredModule,
    undeclared_module,
)
from openhcs.processing.backends.lib_registry import openhcs_registry
from tests.context_support import executing_context

_SOURCE = """CellProfiler Pipeline: https://cellprofiler.org
NamesAndTypes:[module_num:1|enabled:True]
    Assignments count:1
    Select the image type:Grayscale image
    Name to assign these images:DNA
    Select the rule criteria:and (file does contain "DNA")
"""

_UNDECLARED_IN_THE_MIDDLE = (
    _SOURCE
    + """GaussianFilter:[module_num:2|variable_revision_number:1|enabled:True]
    Select the input image:DNA
    Name the output image:Smoothed
    Sigma:2
SomeLabsPlugin:[module_num:3|variable_revision_number:4|enabled:True]
    Select the input image:Smoothed
    Name the output image:Special
    Strength:0.5
GaussianFilter:[module_num:4|variable_revision_number:1|enabled:True]
    Select the input image:Special
    Name the output image:Final
    Sigma:1
"""
)

_UNDECLARED_OBJECT_PRODUCER = (
    _SOURCE
    + """RunCellpose:[module_num:2|variable_revision_number:3|enabled:True]
    Select the input image:DNA
    Detection mode:nuclei
    Name the output object:Nuclei
MeasureObjectSizeShape:[module_num:3|variable_revision_number:3|enabled:True]
    Select object sets to measure:Nuclei
    Calculate the Zernike features?:No
    Calculate the advanced features?:No
MeasureObjectIntensity:[module_num:4|variable_revision_number:4|enabled:True]
    Select images to measure:DNA
    Select objects to measure:Nuclei
"""
)


def _import(tmp_path: Path, text: str) -> tuple[list[FunctionStep], PipelineConfig]:
    cppipe_path = tmp_path / "pipeline.cppipe"
    cppipe_path.write_text(text, encoding="utf-8")
    return import_cellprofiler_pipeline(cppipe_path)


def _kwargs(step: FunctionStep) -> dict[str, object]:
    (invocation,) = normalize_function_pattern(step.func).iter_items()
    return dict(invocation.kwargs_dict)


def _compile_contracts(steps: list[FunctionStep], pipeline_config: PipelineConfig):
    """Build the pipeline's invocation contracts the way compilation does."""

    global_config = GlobalPipelineConfig()
    ensure_global_config_context(GlobalPipelineConfig, global_config)
    ObjectStateRegistry.clear()
    pipeline_state = ObjectState(pipeline_config, scope_id="pipeline")
    try:
        ObjectStateRegistry.register(pipeline_state, _skip_snapshot=True)
        resolved_steps = []
        for index, step in enumerate(steps):
            step_state = ObjectState(
                step,
                scope_id=f"pipeline::functionstep_{index}",
                parent_state=pipeline_state,
            )
            ObjectStateRegistry.register(step_state, _skip_snapshot=True)
            resolved_steps.append(step_state.to_saved_resolved_object())
        session = CompilationSession.from_context(
            context=executing_context(
                step_plans={
                    index: CompiledStepPlan(
                        step_index=index,
                        step_name=step.name,
                        axis_id="A01",
                    )
                    for index, step in enumerate(resolved_steps)
                },
                axis_id="A01",
            ),
            orchestrator=SimpleNamespace(pipeline_config=pipeline_state.to_object()),
            global_config=global_config,
            pipeline=ResolvedPipelineDefinition(
                steps=resolved_steps,
                step_scope_ids={
                    index: f"pipeline::functionstep_{index}"
                    for index in range(len(resolved_steps))
                },
                step_provenance={index: {} for index in range(len(resolved_steps))},
            ),
        )
        return PipelineInvocationContractProviderAuthority.provider_for_pipeline(
            session.pipeline
        )
    finally:
        ObjectStateRegistry.clear()


def test_undeclared_module_becomes_one_wired_step_that_cannot_compile(
    tmp_path: Path,
) -> None:
    steps, pipeline_config = _import(tmp_path, _UNDECLARED_IN_THE_MIDDLE)

    assert [step.name for step in steps] == [
        "GaussianFilter",
        "SomeLabsPlugin",
        "GaussianFilter",
    ]
    assert _kwargs(steps[1]) == {
        "module_name": "SomeLabsPlugin",
        "variable_revision_number": 4,
        "settings": (
            ("Select the input image", "Smoothed"),
            ("Name the output image", "Special"),
            ("Strength", "0.5"),
        ),
        "input_images": "Smoothed",
        "output_images": "Special",
    }
    # The later module reads the undeclared step's output from the main flow.
    assert steps[2].processing_config.input_source.__name__ == "ReadPreviousStep"

    source = FunctionStepTransportAuthority.source_from_pipeline(steps)
    namespace: dict[str, object] = {}
    exec(compile(source, "undeclared_pipeline.py", "exec"), namespace)
    reconstructed = FunctionStepTransportAuthority.pipeline_steps_from_namespace(
        namespace
    )
    assert FunctionStepTransportAuthority.source_from_pipeline(reconstructed) == source
    assert _kwargs(reconstructed[1]) == _kwargs(steps[1])

    message = (
        "CellProfiler module 'SomeLabsPlugin' has no OpenHCS implementation, so "
        "this step cannot run. Replace the step's function with a custom "
        "function producing image 'Special'."
    )
    with pytest.raises(ValueError) as compile_error:
        _compile_contracts(steps, pipeline_config)
    assert str(compile_error.value) == (
        "CellProfiler contract compilation failed for step 1 ('SomeLabsPlugin'), "
        "invocation FunctionInvocationKey(function_name='undeclared_module', "
        f"group_key='default', position=0), module UndeclaredModule: {message}"
    )
    with pytest.raises(NotImplementedError) as call_error:
        undeclared_module(None, **_kwargs(steps[1]))
    assert str(call_error.value) == message


def test_replacing_the_undeclared_step_function_lets_the_pipeline_compile(
    tmp_path: Path,
) -> None:
    steps, pipeline_config = _import(tmp_path, _UNDECLARED_IN_THE_MIDDLE)
    (replacement,) = normalize_function_pattern(steps[0].func).iter_items()

    steps[1].func = (
        replacement.contract.resolve_canonical_raw_callable(),
        {"sigma": 3.0, "name_the_output_image": "Special"},
    )

    assert _compile_contracts(steps, pipeline_config) is not None


def test_undeclared_module_provides_objects_a_measurement_module_reads(
    tmp_path: Path,
) -> None:
    steps, _pipeline_config = _import(tmp_path, _UNDECLARED_OBJECT_PRODUCER)

    assert [step.name for step in steps] == [
        "RunCellpose",
        "MeasureObjectSizeShape",
        "MeasureObjectIntensity",
    ]
    kwargs = _kwargs(steps[0])
    assert kwargs["input_images"] == "DNA"
    assert kwargs["output_objects"] == "Nuclei"
    assert "output_images" not in kwargs


def test_nearest_preceding_undeclared_module_provides_a_shared_name(
    tmp_path: Path,
) -> None:
    steps, _pipeline_config = _import(
        tmp_path,
        _SOURCE
        + """FirstPlugin:[module_num:2|enabled:True]
    Name the output image:Special
FirstPlugin:[module_num:3|enabled:False]
    Name the output image:Final
SecondPlugin:[module_num:4|enabled:True]
    Select the input image:Special
    Name the output image:Special
GaussianFilter:[module_num:5|enabled:True]
    Select the input image:Special
    Name the output image:Final
    Sigma:1
""",
    )

    assert [step.name for step in steps] == [
        "FirstPlugin",
        "SecondPlugin",
        "GaussianFilter",
    ]
    assert "output_images" not in _kwargs(steps[0])
    assert _kwargs(steps[1])["output_images"] == "Special"


def test_adjacent_undeclared_modules_stay_separate_steps(tmp_path: Path) -> None:
    steps, _pipeline_config = _import(
        tmp_path,
        _SOURCE
        + """FirstPlugin:[module_num:2|enabled:True]
    Select the input image:DNA
SecondPlugin:[module_num:3|enabled:True]
    Select the input image:DNA
SecondPlugin:[module_num:4|enabled:True]
    Select the input image:DNA
""",
    )

    assert [(step.name, _kwargs(step)["module_name"]) for step in steps] == [
        ("FirstPlugin", "FirstPlugin"),
        ("SecondPlugin", "SecondPlugin"),
        ("SecondPlugin", "SecondPlugin"),
    ]


def test_name_no_undeclared_module_carries_stays_an_unknown_artifact(
    tmp_path: Path,
) -> None:
    with pytest.raises(
        UnknownArtifactInput,
        match="Module GaussianFilter references unknown image artifact 'Elsewhere'",
    ):
        _import(
            tmp_path,
            _SOURCE
            + """SomeLabsPlugin:[module_num:2|enabled:True]
    Name the output image:Special
GaussianFilter:[module_num:3|enabled:True]
    Select the input image:Elsewhere
    Name the output image:Final
    Sigma:1
""",
        )


def test_declared_pipeline_takes_no_undeclared_path(monkeypatch) -> None:
    """Every hook the undeclared member overrides is inert for declared modules."""

    hooks = (
        "adjacent_blocks_share_step",
        "block_in_artifact_context",
        "block_providing_artifact",
        "validate_compilation",
    )
    overriding = {
        module_type
        for module_type in CellProfilerModule.__registry__.values()
        for hook in hooks
        if hook in vars(module_type)
    }
    assert overriding == {UndeclaredModule}

    def fail(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("a declared pipeline asked for a derived output")

    monkeypatch.setattr(pipeline_import, "_modules_providing_unknown_input", fail)
    (case,) = (case for case in in_tree_cppipe_corpus() if case.name == "ExampleHuman")
    for module in CPPipeParser().parse(case.cppipe_path):
        assert CellProfilerModule.declaration_for_block(
            module
        ) is CellProfilerModule.require_module(module.name)
    steps, _pipeline_config = import_cellprofiler_pipeline(case.cppipe_path)
    assert all(
        CellProfilerModule.require_callable_contract_owner(invocation.contract)
        is not UndeclaredModule
        for step in steps
        for invocation in normalize_function_pattern(step.func).iter_items()
    )


def _absent_distribution_requirements(monkeypatch) -> None:
    monkeypatch.setattr(
        openhcs_registry,
        "_openhcs_requirements",
        lambda: (
            Requirement('absent-probe>=1; extra == "probe"'),
            Requirement('absent-probe>=1; extra == "everything"'),
            Requirement('numpy>=1; extra == "everything"'),
        ),
    )
    monkeypatch.setattr(
        openhcs_registry, "_openhcs_extras", lambda: ("everything", "probe")
    )


def test_declared_module_with_absent_distribution_imports_and_cannot_compile(
    tmp_path: Path,
    monkeypatch,
) -> None:
    _absent_distribution_requirements(monkeypatch)
    # The package attribute of this name is the function; the file is the module.
    gaussian_filter_type = CellProfilerModule.require_module("GaussianFilter")
    monkeypatch.setattr(
        importlib.import_module(gaussian_filter_type.__module__),
        "REQUIRED_DISTRIBUTIONS",
        ("absent-probe",),
        raising=False,
    )

    steps, _pipeline_config = _import(
        tmp_path,
        _SOURCE
        + """GaussianFilter:[module_num:2|enabled:True]
    Select the input image:DNA
    Name the output image:Smoothed
    Sigma:2
""",
    )

    (invocation,) = normalize_function_pattern(steps[0].func).iter_items()
    assert invocation.contract.function_name == "gaussian_filter"
    assert invocation.kwargs_dict["sigma"] == 2.0
    with pytest.raises(ValueError) as error:
        FuncStepContractValidator.validate_external_library_installation(
            invocation.contract.func,
            steps[0].name,
        )
    assert (
        "Function 'gaussian_filter' in step 'GaussianFilter' requires external "
        "library 'absent-probe' which is not installed."
    ) in str(error.value)
    assert "Install with: pip install 'openhcs[probe]'" in str(error.value)


def test_install_command_names_the_narrowest_extra_or_the_distribution(
    monkeypatch,
) -> None:
    _absent_distribution_requirements(monkeypatch)

    assert (
        openhcs_registry.install_command_for_distributions(
            ("absent-probe", "numpy", "no-extra-brings-this")
        )
        == "pip install 'openhcs[probe,everything]' no-extra-brings-this"
    )


@pytest.mark.parametrize(
    "requirement, cataloged",
    [
        ('absent-catalog-probe>=1; extra == "probe"', False),
        ('numpy>=1; extra == "probe"', True),
    ],
)
def test_catalog_module_cannot_hand_over_a_function_its_file_excludes(
    tmp_path: Path,
    monkeypatch,
    requirement: str,
    cataloged: bool,
) -> None:
    distribution = Requirement(requirement).name
    package_name = f"catalog_handover_probe_{distribution.replace('-', '_')}"
    package = tmp_path / package_name
    package.mkdir()
    (package / "__init__.py").write_text(
        "import sys\n"
        "from openhcs.processing.backends.lib_registry.openhcs_registry import (\n"
        "    OpenHCSFunctionCatalogModule,\n"
        ")\n"
        "class Catalog(OpenHCSFunctionCatalogModule):\n"
        "    def openhcs_registry_functions(self):\n"
        f"        from {package_name}.implementation import process\n"
        "        return (process,)\n"
        "sys.modules[__name__].__class__ = Catalog\n"
    )
    (package / "implementation.py").write_text(
        "from openhcs.core.memory.decorators import numpy\n"
        f"REQUIRED_DISTRIBUTIONS = ({distribution!r},)\n"
        "@numpy\n"
        "def process(image):\n"
        "    import absent_catalog_probe\n"
        "    return image\n"
    )
    monkeypatch.syspath_prepend(str(tmp_path))
    monkeypatch.setenv("OPENHCS_CPU_ONLY", "1")
    monkeypatch.setattr(
        openhcs_registry,
        "_openhcs_requirements",
        lambda: (Requirement(requirement),),
    )
    registry = openhcs_registry.OpenHCSRegistry()
    registry.MODULES_TO_SCAN = [package_name, f"{package_name}.implementation"]

    try:
        functions = registry.discover_functions()
    finally:
        for name in (package_name, f"{package_name}.implementation"):
            sys.modules.pop(name, None)

    assert [metadata.original_name for metadata in functions.values()] == (
        ["process"] if cataloged else []
    )


def test_declaration_file_that_fails_to_import_is_not_reported_absent(
    tmp_path: Path,
    monkeypatch,
) -> None:
    """Full discovery skips a broken file; the lookup by key must not."""

    package_name = "declaration_import_failure_probe"
    package = tmp_path / package_name
    package.mkdir()
    (package / "__init__.py").write_text(
        "from typing import ClassVar\n"
        "from metaclass_registry import (\n"
        "    AutoRegisterMeta, LazyDiscoveryDict, RegistryConfig,\n"
        ")\n"
        "from openhcs.processing.backends.lib_registry.openhcs_registry import (\n"
        "    OpenHCSFunctionCatalogDeclaration,\n"
        ")\n"
        "REGISTRY = LazyDiscoveryDict(enable_cache=False)\n"
        "class Declaration(\n"
        "    OpenHCSFunctionCatalogDeclaration,\n"
        "    metaclass=AutoRegisterMeta,\n"
        "    registry_config=RegistryConfig(\n"
        "        registry_dict=REGISTRY,\n"
        "        key_attribute='module_name',\n"
        "        skip_if_no_key=True,\n"
        "        registry_name='probe declaration',\n"
        f"        discovery_package={package_name!r},\n"
        "    ),\n"
        "):\n"
        "    __registry__ = REGISTRY\n"
        "    __registry_key__ = 'module_name'\n"
        "    __skip_if_no_key__ = True\n"
        "    module_name: ClassVar[str | None] = None\n"
        f"    registry_catalog_module: ClassVar[str] = {package_name!r}\n"
        "    @classmethod\n"
        "    def declared_function_names(cls):\n"
        "        return ()\n"
    )
    (package / "working.py").write_text(
        f"from {package_name} import Declaration\n"
        "class Working(Declaration):\n"
        "    module_name = 'Working'\n"
    )
    (package / "broken.py").write_text(
        "import absent_declaration_dependency\n"
        f"from {package_name} import Declaration\n"
        "class Broken(Declaration):\n"
        "    module_name = 'Broken'\n"
    )
    monkeypatch.syspath_prepend(str(tmp_path))
    try:
        import declaration_import_failure_probe as probe

        def lookup(key: str) -> tuple[type, ...]:
            return probe.Declaration.discover_source_declarations(
                frozenset((key,)),
                ("module_name",),
                str,
                lambda declaration: frozenset((declaration.module_name,)),
            )

        assert sorted(probe.REGISTRY) == ["Working"]
        assert [declaration.__name__ for declaration in lookup("Working")] == [
            "Working"
        ]
        assert lookup("NeverDeclared") == ()
        with pytest.raises(ModuleNotFoundError, match="absent_declaration_dependency"):
            lookup("Broken")
    finally:
        for name in tuple(sys.modules):
            if name.partition(".")[0] == package_name:
                del sys.modules[name]
