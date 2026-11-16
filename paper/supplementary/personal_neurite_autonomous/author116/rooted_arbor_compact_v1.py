from dataclasses import dataclass, asdict
import numpy as np
from openhcs.core.memory import numpy
from openhcs.core.pipeline.function_contracts import artifact_inputs, artifact_outputs
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.measurement_row_materialization import DataclassMeasurementColumnarRows
from openhcs.core.runtime_spatial_graph import SpatialGraph
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.processing.backends.analysis.metaxpress_utils import HiddenPixelSize
from openhcs.processing.backends.analysis.neurite_outgrowth import (
    CellProfilerNeuriteEngineProfile, CELLPROFILER_NEURITE_ENGINE_PROFILE,
    MetaXpressCellBodySettings, MetaXpressOutgrowthSettings,
    MetaXpressNuclearSettings, NeuriteIllumination,
)

@dataclass(frozen=True)
class _CompactShaftBody(MetaXpressCellBodySettings):
    shaft_width_px: float = 1.0

    def separate_terminal_shafts(self, body, nuclear_seed, maximum_shaft_width_px):
        return super().separate_terminal_shafts(body, nuclear_seed, self.shaft_width_px)

@numpy(contract=ProcessingContract.PURE_3D)
@artifact_outputs(*(CellProfilerNeuriteEngineProfile.artifact_outputs()[:6] + CellProfilerNeuriteEngineProfile.artifact_outputs()[-1:]))
@artifact_inputs("pixel_size")
def rooted_arbor_compact_v1(
    image,
    neurite_channel_index: int = 1,
    illumination: NeuriteIllumination = NeuriteIllumination.FLUORESCENCE,
    cell_body: MetaXpressCellBodySettings = MetaXpressCellBodySettings(),
    outgrowth: MetaXpressOutgrowthSettings = MetaXpressOutgrowthSettings(),
    use_nuclear_stain: bool = True,
    nuclear_stain: MetaXpressNuclearSettings = MetaXpressNuclearSettings(),
    soma_terminal_shaft_width_um: float = 12.0,
    pixel_size: HiddenPixelSize = HiddenPixelSize(1.0),
) -> tuple[np.ndarray, DataclassMeasurementColumnarRows, DataclassMeasurementColumnarRows,
           np.ndarray, np.ndarray, np.ndarray, np.ndarray, SpatialGraph]:
    """Run the existing rooted-arbor engine with an independent soma shaft scale.

    Input is pipeline-assembled CYX in consumed intensity units. Source XY
    calibration supplies pixel_size. Only the existing terminal-shaft body
    separation method receives the separate physical width; neurite opening,
    root adjacency and topology retain outgrowth.maximum_width.
    The same engine computes its original result.
    Persist only its summary, per-cell rows, four label families and morphology
    graph with unchanged main image; diagnostic planes remain in bounded trials.
    No file I/O or private-state mutation occurs.
    Empty spatial planes fail explicitly; blank nonempty planes use the engine's
    original empty-object behavior. This is an assay-specific exploratory control.
    """
    array = np.asarray(image)
    if array.ndim != 3 or not array.shape[1] or not array.shape[2]:
        raise ValueError("Expected nonempty spatial CYX input")
    scale = float(pixel_size)
    if not np.isfinite(scale) or scale <= 0:
        raise ValueError("Source pixel size must be finite and positive")
    if not np.isfinite(soma_terminal_shaft_width_um) or soma_terminal_shaft_width_um <= 0:
        raise ValueError("Soma shaft width must be finite and positive")
    body = _CompactShaftBody(**asdict(cell_body), shaft_width_px=soma_terminal_shaft_width_um / scale)
    result = CELLPROFILER_NEURITE_ENGINE_PROFILE.analyze(
        image, neurite_channel_index=neurite_channel_index,
        illumination=illumination, cell_body=body, outgrowth=outgrowth,
        use_nuclear_stain=use_nuclear_stain, nuclear_stain=nuclear_stain,
        coordinate_spacing=SourceVoxelSpacing((scale, scale)),
    )
    return result[:7] + result[-1:]
