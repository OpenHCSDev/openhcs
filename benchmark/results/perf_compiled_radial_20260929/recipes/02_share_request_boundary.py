from pathlib import Path
from nominal_refactor_advisor.codemod import (
    CodemodPlanDocument,
    CodemodSourceSnapshot,
    PatchTargetOperation,
    RefactorRecipe,
    SourceRewriteTarget,
    SourceTextReplacement,
)

root = Path(__file__).resolve().parents[4]
path = root / "openhcs/processing/backends/cellprofiler/intensity_distribution.py"
source = path.read_text()
factory = '''    @classmethod
    def from_geometry(
        cls,
        image: np.ndarray,
        labels: np.ndarray,
        geometry: RadialLabelGeometry,
        *,
        bin_count: int,
        wants_scaled: bool,
        maximum_radius: int,
    ) -> "RadialDistributionMeasureRequest":
        """Project a measurement request from the shared label geometry."""
        return cls(
            image=image,
            labels=labels,
            d_to_edge=geometry.d_to_edge,
            d_from_center=geometry.center_fields.d_from_center,
            center_labels=geometry.center_fields.center_labels,
            centers_i=geometry.center_fields.centers_i,
            centers_j=geometry.center_fields.centers_j,
            bin_count=bin_count,
            wants_scaled=wants_scaled,
            maximum_radius=maximum_radius,
        )

'''
start = source.index("class RadialDistributionMeasureRequest:")
end = source.index("\n\n@dataclass", start)
request = source[start:end]
new_request = request.replace("    def arrays(\n", factory + "    def arrays(\n", 1)
guards = """        if any(
            array.shape != image_array.shape
            for array in (d_to_edge_array, d_from_center_array, center_labels_array)
        ):
            raise ValueError("Radial distribution geometry must match the image shape.")
        if centers_i_array.ndim != 1 or centers_i_array.shape != centers_j_array.shape:
            raise ValueError("Radial distribution center coordinates must be equal-length vectors.")
        if int(center_labels_array.max(initial=0)) > centers_i_array.size:
            raise ValueError("Radial distribution center labels exceed the declared center coordinates.")
"""
new_request = new_request.replace(
    "        if self.bin_count <= 0:\n", guards + "        if self.bin_count <= 0:\n", 1
)
old_parent = """            RadialDistributionMeasureRequest(
                image=image,
                labels=labels_array,
                d_to_edge=geometry.d_to_edge,
                d_from_center=geometry.center_fields.d_from_center,
                center_labels=geometry.center_fields.center_labels,
                centers_i=geometry.center_fields.centers_i,
                centers_j=geometry.center_fields.centers_j,
                bin_count=bin_count,
                wants_scaled=wants_scaled,
                maximum_radius=maximum_radius,
            )"""
new_parent = """            RadialDistributionMeasureRequest.from_geometry(
                image,
                labels_array,
                geometry,
                bin_count=bin_count,
                wants_scaled=wants_scaled,
                maximum_radius=maximum_radius,
            )"""
start = source.index(
    "        index = RadialDistributionGeometryIndex(",
    source.index("class NumbaNumpyRadialDistributionBackendStrategy"),
)
end = source.index("        outputs: list[RadialDistributionArrays] = []", start)
old_index = source[start:end]
new_index = """        components = tuple(
            RadialDistributionMeasureRequest.from_geometry(
                image,
                labels_array,
                geometry,
                bin_count=bin_count,
                wants_scaled=wants_scaled,
                maximum_radius=maximum_radius,
            ).arrays()
            for image in images
        )
        if not components:
            return ()
        (
            _image,
            labels_array,
            d_to_edge,
            d_from_center,
            center_labels,
            centers_i,
            centers_j,
        ) = components[0]
        index = RadialDistributionGeometryIndex(
            *_radial_distribution_geometry_index_numba(
                labels_array,
                d_to_edge,
                d_from_center,
                center_labels,
                centers_i,
                centers_j,
                int(bin_count),
                bool(wants_scaled),
                int(maximum_radius),
                object_count,
            )
        )
"""
start = source.index(
    "        outputs: list[RadialDistributionArrays] = []",
    source.index("class NumbaNumpyRadialDistributionBackendStrategy"),
)
end = source.index("\n\ndef radial_distribution_backend(", start)
old_outputs = source[start:end]
new_outputs = old_outputs.replace(
    "        for image in images:",
    "        for image, *_geometry_arrays in components:",
    1,
).replace("                np.ascontiguousarray(image),", "                image,", 1)
replacements = tuple(
    SourceTextReplacement(old_source=a, new_source=b)
    for a, b in (
        (request, new_request),
        (old_parent, new_parent),
        (old_index, new_index),
        (old_outputs, new_outputs),
    )
)
recipe = RefactorRecipe(
    recipe_id="share-radial-request-construction-and-array-boundary",
    operations=(
        PatchTargetOperation(
            target=SourceRewriteTarget(file_path=str(path)),
            replacements=replacements,
            rationale="The existing request owns aligned kernel arguments. Both scalar and batched consumers derive from its geometry projection and validation, avoiding unchecked compiled indexing and duplicate geometry casts. No new carrier, registry or fallback. Authored source/body behavior requires malformed-input and production parity checks.",
        ),
    ),
    reason="Selecting compiled kernels requires their actual arrays to share the existing nominal request boundary; reuse its owner rather than adding consumer-specific guards.",
)
plan = CodemodPlanDocument(recipes=(recipe,))
simulation = plan.simulate(
    CodemodSourceSnapshot.from_source_mapping({str(path): source})
)
assert simulation.is_clean, simulation.simulation_payload()
(
    root.parent
    / "openhcs-benchmark-runs/perf-radial-request-boundary-nra-projected-20260929.diff"
).write_text(simulation.unified_diff({str(path): source}))
print(simulation.apply())
