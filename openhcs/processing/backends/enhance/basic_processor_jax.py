"""Real BaSiCPy correction of independent, same-channel observations."""

from __future__ import annotations

import numpy as np
from basicpy import BaSiC
from basicpy.basicpy import FittingMode

from openhcs.constants.constants import GroupBy
from openhcs.core.artifacts import (
    ArtifactSidecarRole,
    ArtifactSpec,
    ArtifactViewerStreaming,
    ImageArtifactType,
    MainFlowPlaneProjectionOutputSpec,
    MainFlowStackOutputSpec,
)
from openhcs.core.config import DtypeConfig
from openhcs.core.memory import numpy as numpy_func
from openhcs.core.pipeline.function_contracts import (
    allowed_group_by,
    artifact_outputs,
    required_variable_components,
)
from openhcs.processing.backends.enhance.flatfield import FittedIlluminationFieldOutput
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.processing.materialization import (
    ImageFileOptions,
    MaterializationSpec,
    MaterializedFilenameIdentity,
)


def _fitted_field_output(name: str) -> ArtifactSpec:
    """Project group lineage; runtime field owns aggregate contributor context."""
    return MainFlowPlaneProjectionOutputSpec.output(
        name,
        ImageArtifactType,
        sidecar_role=ArtifactSidecarRole.QA_CHECKPOINT,
        materialization=MaterializationSpec(
            ImageFileOptions(
                filename_suffix=".tif",
                filename_identity=MaterializedFilenameIdentity.ARTIFACT_NAME,
            )
        ),
        viewer_streaming=ArtifactViewerStreaming.ON_DEMAND,
    )


CORRECTED_OUTPUT = MainFlowStackOutputSpec.output("basic_corrected", ImageArtifactType)
FLATFIELD_OUTPUT = _fitted_field_output("basic_flatfield")
DARKFIELD_OUTPUT = _fitted_field_output("basic_darkfield")


@numpy_func(contract=ProcessingContract.PURE_3D, dtype_config_default=DtypeConfig())
@allowed_group_by(GroupBy.CHANNEL)
@required_variable_components(FittedIlluminationFieldOutput.observation_axis)
@artifact_outputs(CORRECTED_OUTPUT, FLATFIELD_OUTPUT, DARKFIELD_OUTPUT)
def basic_flatfield_correction_jax(
    image: np.ndarray,
    max_iterations: int = 50,
    epsilon: float = 0.1,
    smoothness_flatfield: float = 1.0,
    smoothness_darkfield: float = 1.0,
    sparse_cost_darkfield: float = 0.01,
    get_darkfield: bool = False,
    fitting_mode: FittingMode = FittingMode.ladmap,
    working_size: int | None = 128,
) -> tuple[np.ndarray, FittedIlluminationFieldOutput, FittedIlluminationFieldOutput]:
    """Fit one BaSiC model to independent observations and apply its fields.

    The leading N axis contains independent timepoints or mosaic positions,
    not channels or the Z planes of a single volume. In a FunctionStep use
    group_by=CHANNEL and variable_components=[SITE] to fit across mosaic fields.
    Z-only stacks are not independent-observation ensembles and are rejected
    by the declared SITE requirement before pipeline execution.
    BaSiCPy's public fit/transform boundary uses NumPy arrays; its internal JAX
    solver does not imply JAX-array transport or require a GPU. CPU-only process
    policy selects the solver's CPU platform before importing the dependency.
    All observations must share a spatial grid and acquisition illumination.
    Several diverse observations are needed to separate stationary shading
    from biology; two is only a minimum input sanity check, not identifiability.

    Args:
        image: Same-channel observations, (N,Y,X) or volumes (N,Z,Y,X).
        max_iterations: Maximum iterations per BaSiC optimization.
        epsilon: BaSiC weight regularization term.
        smoothness_flatfield: Flatfield smoothness weight.
        smoothness_darkfield: Darkfield smoothness weight.
        sparse_cost_darkfield: Darkfield sparse-cost weight.
        get_darkfield: Estimate additive darkfield as well as flatfield.
        fitting_mode: BaSiCPy's declared optimization algorithm.
        working_size: Spatial working size, or None for no rescaling.

    Returns:
        Corrected observations, fitted flatfield and fitted darkfield, all from
        this same fit. The first image remains the pipeline's main flow; fields
        are persisted image sidecars, available for on-demand inspection. When
        get_darkfield=False the darkfield is the model's zero additive field.
        Floating-point corrected observations retain the input shape. BaSiC's
        (image - darkfield) / flatfield retains intensity units, fractions and
        negative values; no clipping, normalization, integer recast or temporal
        baseline subtraction is applied. Values can exceed the input range.
    """
    observations = np.asarray(image)
    if observations.ndim not in (3, 4):
        raise ValueError("BaSiC requires (N,Y,X) or (N,Z,Y,X) observations.")
    if observations.shape[0] < 2:
        raise ValueError("BaSiC requires multiple independent observations.")
    if not np.isfinite(observations).all():
        raise ValueError("BaSiC observations must contain only finite values.")
    FittedIlluminationFieldOutput.validate_observation_domain(image)

    model = BaSiC(
        max_iterations=max_iterations,
        epsilon=epsilon,
        smoothness_flatfield=smoothness_flatfield,
        smoothness_darkfield=smoothness_darkfield,
        sparse_cost_darkfield=sparse_cost_darkfield,
        get_darkfield=get_darkfield,
        fitting_mode=fitting_mode,
        working_size=working_size,
    )
    corrected = model.fit_transform(observations, timelapse=False)
    observation_count = observations.shape[0]
    return (
        np.asarray(corrected),
        FittedIlluminationFieldOutput(np.asarray(model.flatfield), observation_count),
        FittedIlluminationFieldOutput(np.asarray(model.darkfield), observation_count),
    )
