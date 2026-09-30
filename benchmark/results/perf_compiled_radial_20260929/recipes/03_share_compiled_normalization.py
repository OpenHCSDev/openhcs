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
replacements = []
start = source.index("class NumbaNumpyRadialDistributionBackendStrategy")
end = source.index("\n\ndef radial_distribution_backend(", start)
old = source[start:end]
new = old
pstart = new.index("    def prepare_backend(")
pend = new.index("\n    def measure(", pstart)
new = new[:pstart] + '''    def prepare_backend(self) -> None:
        labels = np.zeros((8, 8), dtype=np.int32)
        labels[2:6, 2:6] = 1
        geometry = self.label_geometry(labels)
        for dtype in (np.float32, np.float64):
            image = np.zeros(labels.shape, dtype=dtype)
            self.measure_self_centered_with_geometry(
                image,
                labels,
                geometry,
                bin_count=4,
                wants_scaled=True,
                maximum_radius=100,
            )
            self.measure_batch_self_centered_with_geometry(
                (image, image),
                labels,
                geometry,
                bin_count=4,
                wants_scaled=True,
                maximum_radius=100,
            )

    def arrays_from_bin_totals(
        self,
        histogram: np.ndarray,
        number_at_distance: np.ndarray,
        radial_values: np.ndarray,
        radial_counts: np.ndarray,
    ) -> RadialDistributionArrays:
        """Normalize scalar and batched accumulations through one kernel."""
        (
            fraction_at_distance,
            mean_pixel_fraction,
            radial_cv_by_bin,
            object_has_pixels,
        ) = _radial_distribution_arrays_from_bin_totals_numba(
            histogram, number_at_distance, radial_values, radial_counts
        )
        return RadialDistributionArrays.from_components(
            fraction_at_distance=fraction_at_distance,
            mean_pixel_fraction=mean_pixel_fraction,
            radial_cv_by_bin=radial_cv_by_bin,
            object_has_pixels=object_has_pixels,
            n_bins=radial_values.shape[0],
        )
''' + new[pend:]
a = new.index("        n_bins = (", new.index("    def measure("))
b = new.index("        if object_count <= 0:", a)
new = new[:a] + new[b:]
a = new.index(
    "        (\n            fraction_at_distance,", new.index("    def measure(")
)
b = new.index("\n    def measure_batch_", a)
oldscalar = new[a:b]
callstart = oldscalar.index("            image_array,")
callend = oldscalar.index("\n        )", callstart)
newscalar = (
    """        return self.arrays_from_bin_totals(
            *_accumulate_radial_distribution_numba(
"""
    + oldscalar[callstart:callend]
    + """
            )
        )
"""
)
new = new[:a] + newscalar + new[b:]
a = new.index("        outputs: list[RadialDistributionArrays] = []")
new = new[:a] + """        return tuple(
            self.arrays_from_bin_totals(
                *_accumulate_radial_distribution_from_geometry_index_numba(
                    image,
                    index.pixel_rows,
                    index.pixel_cols,
                    index.object_indices,
                    index.bin_indices,
                    index.radial_indices,
                    index.number_at_distance,
                    index.radial_counts,
                    index.object_count,
                    index.bin_count,
                    index.n_bins,
                )
            )
            for image, *_geometry_arrays in components
        )
"""
replacements.append((old, new))
for name in (
    "_measure_radial_distribution_from_geometry_index_numba",
    "_measure_radial_distribution_numba",
):
    a = source.index("@njit(cache=True)\ndef " + name + "(")
    b = source.index("\n\n@", a + 1)
    old = source[a:b]
    split = old.index("    fraction_at_distance = np.zeros(")
    new = (
        old[:split].replace(name, name.replace("_measure_", "_accumulate_"), 1)
        + """    return histogram, number_at_distance, radial_values, radial_counts
"""
    )
    replacements.append((old, new))
normalizer = """@njit(cache=True)
def _radial_distribution_arrays_from_bin_totals_numba(
    histogram: np.ndarray,
    number_at_distance: np.ndarray,
    radial_values: np.ndarray,
    radial_counts: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    object_count, distance_bins = histogram.shape
    n_bins = radial_values.shape[0]
    # Fractions are real-valued measurements even for integer input images.
    fraction_at_distance = np.zeros(histogram.shape, dtype=np.float64)
    mean_pixel_fraction = np.zeros(histogram.shape, dtype=np.float64)
    object_has_pixels = np.zeros(object_count, dtype=np.bool_)
    intensity_sums = np.sum(histogram, axis=1)
    eps = np.finfo(np.float64).eps
    for object_index in range(object_count):
        pixel_count = 0.0
        for bin_index in range(distance_bins):
            pixel_count += number_at_distance[object_index, bin_index]
        object_has_pixels[object_index] = pixel_count > 0.0
        for bin_index in range(distance_bins):
            fraction = _numpy_divide_scalar(
                histogram[object_index, bin_index], intensity_sums[object_index]
            )
            fraction_at_distance[object_index, bin_index] = fraction
            pixel_fraction = _numpy_divide_scalar(
                number_at_distance[object_index, bin_index], pixel_count
            )
            mean_pixel_fraction[object_index, bin_index] = fraction / (
                pixel_fraction + eps
            )
    radial_cv_by_bin = np.zeros((n_bins, object_count), dtype=np.float64)
    for bin_index in range(n_bins):
        for object_index in range(object_count):
            populated_wedges = 0
            wedge_sum = 0.0
            for radial_index in range(8):
                count = radial_counts[bin_index, object_index, radial_index]
                if count > 0.0:
                    populated_wedges += 1
                    wedge_sum += radial_values[bin_index, object_index, radial_index] / count
            if populated_wedges == 0:
                continue
            mean = wedge_sum / populated_wedges
            squared_deviations = 0.0
            for radial_index in range(8):
                count = radial_counts[bin_index, object_index, radial_index]
                if count > 0.0:
                    deviation = radial_values[bin_index, object_index, radial_index] / count - mean
                    squared_deviations += deviation * deviation
            cv = _numpy_divide_scalar(
                np.sqrt(squared_deviations / populated_wedges), mean
            )
            # Native masked-array division fills undefined coefficients with zero.
            if np.isfinite(cv):
                radial_cv_by_bin[bin_index, object_index] = cv
    return fraction_at_distance, mean_pixel_fraction, radial_cv_by_bin, object_has_pixels


"""
old = replacements[-1][0]
replacements[-1] = (old, replacements[-1][1] + "\n\n" + normalizer.rstrip())
a = source.index("@njit(cache=True)\ndef _radial_cv_divide_scalar(")
b = source.index("\n\n@", a + 1)
replacements.append((source[a:b] + "\n\n", ""))
recipe = RefactorRecipe(
    recipe_id="one-compiled-radial-normalization-authority",
    operations=(
        PatchTargetOperation(
            target=SourceRewriteTarget(file_path=str(path)),
            replacements=tuple(
                SourceTextReplacement(old_source=a, new_source=b)
                for a, b in replacements
            ),
            rationale="Existing compiled backend owns normalization for both scalar and geometry-index accumulators; remove duplicate implementations and private kernel names. Preserve native reference, real-valued integer fractions, centered variance and masked undefined-CV semantics. No new class or registry; existing family preparation derives both floating signatures from public consumers.",
        ),
    ),
    reason="The default promotion exposed integer truncation and duplicate CV logic; consolidate mathematical behavior before performance promotion. Exact source checking is not semantic proof; dtype, production replay and runtime gates remain separate.",
)
plan = CodemodPlanDocument(recipes=(recipe,))
simulation = plan.simulate(
    CodemodSourceSnapshot.from_source_mapping({str(path): source})
)
assert simulation.is_clean, simulation.simulation_payload()
(
    root.parent
    / "openhcs-benchmark-runs/perf-radial-normalization-nra-projected-20260929.diff"
).write_text(simulation.unified_diff({str(path): source}))
print(simulation.apply())
