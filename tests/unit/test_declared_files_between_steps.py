"""A file one step declares it writes is an input of a later step (DL2, part A).

Every test compiles (and where the rule is a run-time one, executes) a real
pipeline over a tiny synthetic plate.
"""

from __future__ import annotations

import io
import pickle
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from queue import SimpleQueue

import pytest

from openhcs.core.vfs_protocol import (
    DeclaredFile,
    DeclaredFileLinkError,
    LinkedInputFile,
    OutputFileOf,
    PlateInputFileDeclaration,
    PlateOutputFileDeclaration,
    SeveralWritersOfDeclaredFileError,
)

IMPORTS = '''
from pathlib import Path
from typing import Optional

from openhcs.core.artifacts.kinds import SpecialArtifactType
from openhcs.core.artifacts.specs import ArtifactSpec
from openhcs.core.callable_contract import FunctionStepExecutionScope
from openhcs.core.memory import numpy as numpy_function
from openhcs.core.pipeline.function_contracts import (
    artifact_inputs,
    artifact_outputs,
    execution_scope,
    runtime_bound_parameters,
)
from openhcs.core.runtime_stores import RuntimeArtifactBatch
from openhcs.core.vfs_protocol import PlateInputFile, PlateOutputFile

dl2_test_patches = ArtifactSpec.input("dl2_test_patches", SpecialArtifactType)
'''

FUNCTIONS = (
    '''
@numpy_function
def dl2_test_write(image, model_file: Optional[PlateOutputFile] = None, write: bool = True):
    """Write a declared output file.

    Args:
        image: stack
        model_file: where to write
        write: whether to write the file at all
    """
    if write:
        Path(model_file).write_text("model")
    return image
''',
    '''
@numpy_function
def dl2_test_read(image, model_file: PlateInputFile):
    """Read a declared input file.

    Args:
        image: stack
        model_file: what to read
    """
    Path(model_file).read_text()
    return image
''',
    '''
@numpy_function
@artifact_outputs(ArtifactSpec.output("dl2_test_patches", SpecialArtifactType))
def dl2_test_emit(image):
    """Return a patch of every stack.

    Args:
        image: stack
    """
    return image, image[:, :8, :8]
''',
    '''
@execution_scope(FunctionStepExecutionScope.PLATE)
@runtime_bound_parameters(RuntimeArtifactBatch)
@artifact_inputs(dl2_test_patches)
@artifact_outputs(ArtifactSpec.output("dl2_test_model", SpecialArtifactType))
def dl2_test_fit_plate(
    *,
    model_file: PlateOutputFile = Path("models/plate.txt"),
    artifact_batch: RuntimeArtifactBatch,
):
    """Write one file for the whole plate.

    Args:
        model_file: where to write
        artifact_batch: patches of every well
    """
    Path(model_file).write_text("plate model")
    return {"wells": sorted(artifact_batch.records(dl2_test_patches.ref()))}
''',
)


class Plates:
    """Synthetic plates and the registered toy functions, built once."""

    def __init__(self, root: Path) -> None:
        from openhcs.processing.custom_functions import CustomFunctionManager

        self.root = root
        self.suffix_count = 0
        self.queue: SimpleQueue = SimpleQueue()
        manager = CustomFunctionManager()
        by_name = {
            function.__name__: function
            for source in FUNCTIONS
            for function in manager.register_from_code(
                IMPORTS + source, persist=False, emit_signal=False
            )
        }
        self.write = by_name["dl2_test_write"]
        self.read = by_name["dl2_test_read"]
        self.emit = by_name["dl2_test_emit"]
        self.fit_plate = by_name["dl2_test_fit_plate"]
        self.one_well = self._plate("one_well", ("A01",), wavelengths=1)
        self.two_wells = self._plate("two_wells", ("A01", "A02"), wavelengths=1)
        self.two_channels = self._plate("two_channels", ("A01",), wavelengths=2)

    def _plate(self, name: str, wells: tuple[str, ...], *, wavelengths: int) -> Path:
        from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator

        plate = self.root / name
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            SyntheticMicroscopyGenerator(
                output_dir=str(plate),
                grid_size=(1, 2),
                tile_size=(64, 64),
                wavelengths=wavelengths,
                z_stack_levels=1,
                num_cells=5,
                cell_size_range=(4, 6),
                wells=list(wells),
                format="ImageXpress",
                random_seed=7,
            ).generate_dataset()
        return plate

    def compile(self, plate: Path, steps, **path_planning):
        """Compile ``steps`` over ``plate`` into a fresh output dataset."""

        from objectstate.lazy_factory import ensure_global_config_context

        from openhcs.core.config import (
            CompilationDebugConfig,
            GlobalPipelineConfig,
            LazyPathPlanningConfig,
            LazyVFSConfig,
            MaterializeToDisk,
            PathPlanningConfig,
            PipelineConfig,
            VFSConfig,
        )
        from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
        from openhcs.core.progress import set_progress_queue
        from openhcs.microscopes.imagexpress import ImageXpressHandler

        self.suffix_count += 1
        path_planning = {
            "output_dir_suffix": f"_out{self.suffix_count}",
            **path_planning,
        }
        vfs = VFSConfig(materialization_backend=MaterializeToDisk)
        ensure_global_config_context(
            GlobalPipelineConfig,
            GlobalPipelineConfig(
                num_workers=1,
                dataset_source=ImageXpressHandler,
                use_threading=False,
                path_planning_config=PathPlanningConfig(**path_planning),
                vfs_config=vfs,
                compilation_debug_config=CompilationDebugConfig(
                    enabled=True,
                    compiled_execution_bundle_path=Path("debug/bundle.pkl"),
                ),
            ),
        )
        set_progress_queue(self.queue)
        orchestrator = PipelineOrchestrator(
            plate,
            pipeline_config=PipelineConfig(
                path_planning_config=LazyPathPlanningConfig(**path_planning),
                vfs_config=LazyVFSConfig.from_config(vfs),
            ),
        ).initialize()
        return orchestrator, orchestrator.compile_pipelines(pipeline_definition=steps)

    def execute(self, orchestrator, bundle, plate: Path):
        from openhcs.core.progress import ProgressExecutionContext, set_progress_queue

        set_progress_queue(self.queue)
        try:
            return orchestrator.execute_compiled_bundle(
                execution_bundle=bundle,
                max_workers=1,
                progress_queue=self.queue,
                progress_context=ProgressExecutionContext(
                    execution_id="dl2", subject_id=str(plate)
                ),
            )
        finally:
            set_progress_queue(None)


@pytest.fixture(scope="module")
def plates(tmp_path_factory) -> Plates:
    return Plates(tmp_path_factory.mktemp("dl2_plates"))


def _step(name: str, func):
    from openhcs.core.steps import FunctionStep

    return FunctionStep(name=name, func=func)


def _sent_to_workers(bundle):
    """Return the compiled contexts as a worker process receives them."""

    return pickle.loads(
        pickle.dumps(bundle.for_transport_serialization().transport_contexts)
    )


def _declared_files(contexts, step_index: int) -> dict[str, tuple[DeclaredFile, ...]]:
    return {
        axis: tuple(
            declared
            for invocation in context.step_plans[
                step_index
            ].compiled_function_pattern.iter_invocations()
            for declared in invocation.declared_files
        )
        for axis, context in contexts.items()
    }


def _failure(results) -> str:
    return " | ".join(
        str(result.error_message)
        for result in results.values()
        if not result.is_success()
    )


def test_output_declarations_resolve_against_the_output_dataset(plates):
    _, bundle = plates.compile(
        plates.one_well,
        [_step("fit", (plates.write, {"model_file": "models/m.txt"}))],
        global_output_folder=Path("elsewhere"),
    )

    (context,) = bundle.runtime_contexts.values()
    output_root = Path(context.output_dataset_root)
    # The folder that defines the output root stays relative to the input plate.
    assert output_root.parent == plates.one_well / "elsewhere"
    (invocation,) = context.step_plans[0].compiled_function_pattern.iter_invocations()
    (declared,) = invocation.declared_files
    assert type(declared) is DeclaredFile
    assert declared.parameter == "model_file"
    assert declared.path == output_root / "models" / "m.txt"
    assert isinstance(declared.declaration, PlateOutputFileDeclaration)
    assert invocation.kwargs_dict["model_file"] == declared.path
    assert (output_root / "debug" / "bundle.pkl").is_file()
    assert not (plates.one_well / "debug").exists()
    assert _declared_files(_sent_to_workers(bundle), 0) == {"A01": (declared,)}


def test_two_wells_writing_one_declared_file_is_a_compile_error(plates):
    with pytest.raises(SeveralWritersOfDeclaredFileError) as raised:
        plates.compile(
            plates.two_wells,
            [_step("fit", (plates.write, {"model_file": "models/m.txt"}))],
        )

    message = str(raised.value)
    assert "models/m.txt has 2 writers" in message
    for writer in ("axis 'A01'", "axis 'A02'"):
        assert (
            f"step 'fit' (index 0) callable 'dl2_test_write' parameter "
            f"'model_file', {writer}, group 'default'" in message
        )


def test_two_groups_of_one_well_writing_one_declared_file_is_a_compile_error(plates):
    from openhcs.core.config import LazyProcessingConfig
    from openhcs.core.steps import FunctionStep
    from openhcs.domains.microscopy.axes import Microscopy

    step = FunctionStep(
        name="fit",
        func={
            "1": (plates.write, {"model_file": "models/m.txt"}),
            "2": (plates.write, {"model_file": "models/m.txt"}),
        },
        processing_config=LazyProcessingConfig(
            variable_components=[Microscopy.Site], group_by=Microscopy.Channel
        ),
    )

    with pytest.raises(SeveralWritersOfDeclaredFileError) as raised:
        plates.compile(plates.two_channels, [step])

    message = str(raised.value)
    assert "axis 'A01', group '1'" in message
    assert "axis 'A01', group '2'" in message


def test_second_call_writing_a_declared_file_in_one_well_is_refused(plates):
    # Default grouping calls the function once per channel; the compiler has one
    # invocation, so the refusal comes from the executor.
    orchestrator, bundle = plates.compile(
        plates.two_channels,
        [_step("fit", (plates.write, {"model_file": "models/m.txt"}))],
    )

    failure = _failure(plates.execute(orchestrator, bundle, plates.two_channels))

    assert "would be written twice in one execution" in failure
    assert failure.count("step 'fit' (index 0) callable 'dl2_test_write'") == 2


def test_step_that_runs_once_for_the_plate_is_one_writer(plates):
    orchestrator, bundle = plates.compile(
        plates.two_wells,
        [_step("emit", plates.emit), _step("fit", plates.fit_plate)],
    )

    results = plates.execute(orchestrator, bundle, plates.two_wells)

    assert not _failure(results)
    paths = {declared.path for files in _declared_files(bundle.runtime_contexts, 1).values() for declared in files}
    (path,) = paths
    assert path.read_text() == "plate model"


def test_linked_input_compiles_without_the_file_and_reads_the_producers_path(plates):
    orchestrator, bundle = plates.compile(
        plates.one_well,
        [
            _step("fit", (plates.write, {"model_file": "models/m.txt"})),
            _step(
                "denoise",
                (
                    plates.read,
                    {"model_file": OutputFileOf(step="fit", parameter="model_file")},
                ),
            ),
        ],
    )

    (context,) = bundle.runtime_contexts.values()
    ((written,),) = _declared_files(bundle.runtime_contexts, 0).values()
    ((linked,),) = _declared_files(bundle.runtime_contexts, 1).values()
    assert not written.path.exists()
    assert type(linked) is LinkedInputFile
    assert linked.path == written.path
    assert isinstance(linked.declaration, PlateInputFileDeclaration)
    assert (linked.producer_step_index, linked.producer_parameter) == (0, "model_file")
    (invocation,) = context.step_plans[1].compiled_function_pattern.iter_invocations()
    assert invocation.kwargs_dict["model_file"] == written.path
    assert _declared_files(_sent_to_workers(bundle), 1) == {"A01": (linked,)}

    assert not _failure(plates.execute(orchestrator, bundle, plates.one_well))
    assert written.path.read_text() == "model"


def test_linked_input_whose_producer_wrote_nothing_fails_before_the_consumer_runs(plates):
    orchestrator, bundle = plates.compile(
        plates.one_well,
        [
            _step("fit", (plates.write, {"model_file": "models/m.txt", "write": False})),
            _step(
                "denoise",
                (
                    plates.read,
                    {"model_file": OutputFileOf(step="fit", parameter="model_file")},
                ),
            ),
        ],
    )

    failure = _failure(plates.execute(orchestrator, bundle, plates.one_well))

    assert "step 'denoise' (index 1) callable 'dl2_test_read'" in failure
    assert "step 'fit' (index 0) declares it writes through 'model_file'" in failure
    assert "does not exist" in failure


def _link(step: str, parameter: str = "model_file"):
    return OutputFileOf(step=step, parameter=parameter)


@pytest.mark.parametrize(
    ("steps", "error", "expected"),
    [
        pytest.param(
            lambda p: [
                _step("denoise", (p.read, {"model_file": _link("fit")})),
                _step("fit", (p.write, {"model_file": "models/m.txt"})),
            ],
            DeclaredFileLinkError,
            "step 'denoise' (index 0) callable dl2_test_read.model_file reads the "
            "file step 'fit' (index 1) writes through 'model_file', but that step "
            "does not run earlier",
            id="later step",
        ),
        pytest.param(
            lambda p: [_step("denoise", (p.read, {"model_file": _link("fit")}))],
            DeclaredFileLinkError,
            "the pipeline has no step named 'fit'; steps: ['denoise']",
            id="unknown step",
        ),
        pytest.param(
            lambda p: [
                _step("fit", (p.write, {"model_file": "models/a.txt"})),
                _step("fit", (p.write, {"model_file": "models/b.txt"})),
                _step("denoise", (p.read, {"model_file": _link("fit")})),
            ],
            DeclaredFileLinkError,
            "step name 'fit' is shared by the steps at indexes [0, 1]",
            id="ambiguous step",
        ),
        pytest.param(
            lambda p: [
                _step("fit", (p.write, {"model_file": "models/m.txt"})),
                _step("denoise", (p.read, {"model_file": _link("fit", "write")})),
            ],
            DeclaredFileLinkError,
            "parameter 'write' is not a declared output file of step 'fit'; its "
            "output file parameters: ['model_file']",
            id="not an output file parameter",
        ),
        pytest.param(
            lambda p: [
                _step("fit", (p.write, {"write": False})),
                _step("denoise", (p.read, {"model_file": _link("fit")})),
            ],
            DeclaredFileLinkError,
            "step 'fit' callable 'dl2_test_write' has no value for output file "
            "'model_file'",
            id="producer value is None",
        ),
        pytest.param(
            lambda p: [
                _step("fit", (p.write, {"model_file": "models/m.txt"})),
                _step("again", (p.write, {"model_file": _link("fit")})),
            ],
            TypeError,
            "only an input file parameter can read a file another step writes",
            id="output parameter given a link",
        ),
        pytest.param(
            lambda p: [_step("denoise", (p.read, {"model_file": "models/absent.txt"}))],
            FileNotFoundError,
            "Declared input file does not exist",
            id="unlinked missing input",
        ),
    ],
)
def test_declared_file_compile_errors(plates, steps, error, expected):
    with pytest.raises(error) as raised:
        plates.compile(plates.one_well, steps(plates))

    # Every error names the step and the parameter, in its text or its notes.
    report = "\n".join((str(raised.value), *getattr(raised.value, "__notes__", ())))
    assert expected in report
    assert "(index" in report
    assert "model_file" in report
