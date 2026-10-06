from dataclasses import dataclass
import numpy as np
from scipy import ndimage as ndi
from skimage.morphology import h_maxima
from skimage.segmentation import watershed
from openhcs.core.memory import numpy
from openhcs.core.artifacts import (ImageArtifactType, MainFlowStackOutputSpec, MeasurementsArtifactType, ObjectLabelsArtifactType, ObjectMeasurementSubjectRelation, ArtifactSpec, SpecialArtifactType)
from openhcs.core.measurement_row_materialization import DataclassMeasurementColumnarRows
from openhcs.core.pipeline.function_contracts import artifact_outputs
from openhcs.core.runtime_measurements import ObjectCoreMeasurementFeature, RuntimeMeasurementFeature, RuntimeMeasurementFeatureOwner
from openhcs.core.aligned_image_payload import AlignedImageSliceContext, pack_aligned_image_outputs
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.processing.materialization import CsvOptions, MaterializationSpec, PointROIOptions, ROIOptions

class CentreExtraFeature(RuntimeMeasurementFeature):
    VOLUME_VOXELS = "volume_voxels"

class CentreFeatureOwner(RuntimeMeasurementFeatureOwner):
    @classmethod
    def owns_measurement_feature_name(cls, feature_name: str) -> bool:
        return any(f.feature_name == feature_name for fs in (ObjectCoreMeasurementFeature, CentreExtraFeature) for f in fs)
    @classmethod
    def owns_primary_measurement_feature_name(cls, feature_name: str) -> bool:
        return cls.owns_measurement_feature_name(feature_name)

@dataclass(frozen=True)
class CentreRow:
    object_label: int
    center_z: float
    center_y: float
    center_x: float
    volume_voxels: int

@dataclass(frozen=True)
class MarkerTopologyRow:
    marker6_id: int
    plateau26_id: int
    support6_id: int
    marker_voxels: int
    distance_peak_voxels: float
    marker_z: float
    marker_y: float
    marker_x: float

@dataclass(frozen=True)
class SeedAssociationRow:
    marker_id: int
    support6_id: int
    peak_z: float
    peak_y: float
    peak_x: float
    peak_distance_voxels: float
    retained: int
    associated_marker_id: int

@dataclass(frozen=True)
class VolumeCountRow:
    image_level_count: int
    threshold_source_units: float
    marker_prominence_voxels: float
    minimum_volume_voxels: int
    marker_connectivity: int
    minimum_separation_z_voxels: float
    minimum_separation_yx_voxels: float

RAW = MainFlowStackOutputSpec.output("h002_raw", ImageArtifactType)
SMOOTH = MainFlowStackOutputSpec.output("h002_smoothed", ImageArtifactType)
SUPPORT = MainFlowStackOutputSpec.output("h002_support", ImageArtifactType)
DISTANCE = MainFlowStackOutputSpec.output("h002_distance", ImageArtifactType)
MARKERS = MainFlowStackOutputSpec.output("h002_markers", ImageArtifactType)
LABEL_IMAGE = MainFlowStackOutputSpec.output("h002_label_image", ImageArtifactType)
LABELS = MainFlowStackOutputSpec.output("h002_labels", ObjectLabelsArtifactType, materialization=MaterializationSpec(ROIOptions(min_area=0)))
ROWS = MainFlowStackOutputSpec.output("h002_centres", MeasurementsArtifactType,
    measurement_feature_owner=CentreFeatureOwner,
    relations=(ObjectMeasurementSubjectRelation(source=LABELS.ref(), id_field="object_label"),),
    materialization=MaterializationSpec(CsvOptions(), PointROIOptions(z_feature=ObjectCoreMeasurementFeature.CENTER_Z, y_feature=ObjectCoreMeasurementFeature.CENTER_Y, x_feature=ObjectCoreMeasurementFeature.CENTER_X)))
COUNT = ArtifactSpec.output("h002_volume_count", SpecialArtifactType, materialization=MaterializationSpec(CsvOptions()))

TOPOLOGY = ArtifactSpec.output("h002_marker_topology", SpecialArtifactType, materialization=MaterializationSpec(CsvOptions()))

ASSOCIATION = ArtifactSpec.output("h002_seed_association", SpecialArtifactType, materialization=MaterializationSpec(CsvOptions()))

@numpy(contract=ProcessingContract.PURE_3D)
@artifact_outputs(RAW, SMOOTH, SUPPORT, DISTANCE, MARKERS, LABEL_IMAGE, LABELS, ROWS, COUNT, TOPOLOGY, ASSOCIATION)
def h002_centres_v3_association(image: np.ndarray, threshold: float = 8000.0, sigma_z: float = 1.0, sigma_yx: float = 2.0, marker_prominence: float = 2.0, min_volume: int = 300, marker_connectivity: int = 3, minimum_separation_z: float = 5.0, minimum_separation_yx: float = 10.0):
    """3D body centroids, ZYX zero-based voxels. Keep boundary fragments; no physical calibration assumed."""
    if image.ndim != 3:
        raise ValueError("Requires complete ZYX volume")
    smooth = ndi.gaussian_filter(image.astype(np.float32), sigma=(sigma_z, sigma_yx, sigma_yx))
    support = ndi.binary_fill_holes(smooth > threshold)
    components, nc = ndi.label(support)
    sizes = np.bincount(components.ravel())
    keep = sizes >= min_volume
    keep[0] = False
    support = keep[components]
    distance = ndi.distance_transform_edt(support).astype(np.float32)
    maxima = h_maxima(distance, marker_prominence) & support
    if marker_connectivity not in (1, 3):
        raise ValueError("Marker connectivity must be1 (6-neighbour) or3 (26-neighbour)")
    maxima6, n6 = ndi.label(maxima)
    maxima26, n26 = ndi.label(maxima, structure=ndi.generate_binary_structure(3, 3))
    support6, ns = ndi.label(support)
    topology = []
    for mid, sl in enumerate(ndi.find_objects(maxima6), start=1):
        if sl is None:
            continue
        local = maxima6[sl] == mid
        offset = np.array([a.start for a in sl])
        coords = np.argwhere(local) + offset
        first = tuple(coords[0])
        ctr = np.mean(coords, axis=0)
        peak = float(np.max(distance[tuple(coords.T)]))
        topology.append(MarkerTopologyRow(mid, int(maxima26[first]), int(support6[first]), len(coords), peak, float(ctr[0]), float(ctr[1]), float(ctr[2])))
    markers, nm = ndi.label(maxima, structure=ndi.generate_binary_structure(3, marker_connectivity))
    seed_candidates = []
    for mid, sl in enumerate(ndi.find_objects(markers), start=1):
        if sl is None:
            continue
        coords = np.argwhere(markers[sl] == mid) + np.array([a.start for a in sl])
        values = distance[tuple(coords.T)]
        peak_index = int(np.argmax(values))
        coord = coords[peak_index]
        seed_candidates.append((mid, int(support6[tuple(coord)]), float(values[peak_index]), coord))
    retained = []
    association = []
    for mid, comp, peak, coord in sorted(seed_candidates, key=lambda a: (-a[2], a[0])):
        owner = mid
        for kept_mid, kept_comp, kept_peak, kept_coord in retained:
            if comp == kept_comp and abs(float(coord[0] - kept_coord[0])) <= minimum_separation_z and float(np.linalg.norm(coord[1:] - kept_coord[1:])) <= minimum_separation_yx:
                owner = kept_mid
                break
        if owner == mid:
            retained.append((mid, comp, peak, coord))
        association.append(SeedAssociationRow(mid, comp, float(coord[0]), float(coord[1]), float(coord[2]), peak, int(owner == mid), owner))
    accepted_ids = [r[0] for r in retained]
    markers = np.where(np.isin(markers, accepted_ids), markers, 0)
    basins = watershed(-distance, markers, mask=support).astype(np.int32)
    objects = []
    labels = np.zeros_like(basins)
    for old, sl in enumerate(ndi.find_objects(basins), start=1):
        if sl is None:
            continue
        local = basins[sl] == old
        volume = int(np.count_nonzero(local))
        if volume < min_volume:
            continue
        new = len(objects) + 1
        labels[sl][local] = new
        ctr = np.array(ndi.center_of_mass(local)) + np.array([s.start for s in sl])
        objects.append(CentreRow(new, float(ctr[0]), float(ctr[1]), float(ctr[2]), volume))
    specs = (RAW, SMOOTH, SUPPORT, DISTANCE, MARKERS, LABEL_IMAGE)
    main = pack_aligned_image_outputs((image, smooth, support.astype(np.uint8), distance, markers, labels), slice_contexts=AlignedImageSliceContext.main_flow_for_artifact_specs(specs))
    counts = (VolumeCountRow(len(objects), threshold, marker_prominence, min_volume, marker_connectivity, minimum_separation_z, minimum_separation_yx),)
    return main, labels, DataclassMeasurementColumnarRows(tuple(objects), row_type=CentreRow), DataclassMeasurementColumnarRows(counts, row_type=VolumeCountRow), DataclassMeasurementColumnarRows(tuple(topology), row_type=MarkerTopologyRow), DataclassMeasurementColumnarRows(tuple(association), row_type=SeedAssociationRow)
