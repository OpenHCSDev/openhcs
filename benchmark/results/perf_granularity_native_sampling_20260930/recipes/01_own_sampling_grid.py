from pathlib import Path
from nominal_refactor_advisor.codemod import CodemodPlanDocument,CodemodSourceSnapshot,PatchTargetOperation,RefactorRecipe,SourceRewriteTarget,SourceTextReplacement
root=Path(__file__).resolve().parents[4];path=root/'openhcs/processing/backends/cellprofiler/granularity.py';source=path.read_text();replacements=[]
new_grid='''@dataclass(frozen=True, slots=True)
class GranularitySamplingGrid:
    """CP logical extent, physical samples and coordinate-grid policy."""

    logical_shape: tuple[float, float]

    def __post_init__(self) -> None:
        if len(self.logical_shape) != 2 or not all(np.isfinite(value) for value in self.logical_shape):
            raise ValueError("Granularity logical grids require two finite dimensions.")
        object.__setattr__(self, "logical_shape", tuple(float(value) for value in self.logical_shape))

    @property
    def array_shape(self) -> tuple[int, int]:
        return tuple(max(0, int(np.ceil(value))) for value in self.logical_shape)

    def subsampled(self, factor: float) -> "GranularitySamplingGrid":
        return type(self)(tuple(value * float(factor) for value in self.logical_shape))

    def coordinate_scales_from(self, source: "GranularitySamplingGrid") -> tuple[float, float]:
        return tuple((source_size - 1.0) / (target_size - 1.0) if target_size > 1.0 else 0.0 for source_size, target_size in zip(source.logical_shape, self.logical_shape, strict=True))

    def sample_pixels(
        self, image: np.ndarray, *, coordinate_scales: tuple[float, float]
    ) -> np.ndarray:
        """Sample origin-scaled coordinates without materializing coordinate planes."""
        image_array = np.asarray(image)
        if image_array.ndim != 2:
            raise ValueError("Granularity sampling requires a 2-D image.")
        dtype = image_array.dtype.newbyteorder("=")
        output = np.empty(self.array_shape, dtype=dtype)
        if np.iscomplexobj(image_array):
            output.real = self.sample_pixels(image_array.real, coordinate_scales=coordinate_scales)
            output.imag = self.sample_pixels(image_array.imag, coordinate_scales=coordinate_scales)
        else:
            _sample_order_one_grid(
                np.ascontiguousarray(image_array, dtype=dtype),
                output,
                float(coordinate_scales[0]),
                float(coordinate_scales[1]),
            )
        return output

    def sample_grid(self, image: np.ndarray, source: "GranularitySamplingGrid") -> np.ndarray:
        """Sample another logical grid with CP endpoint coordinate scales."""
        return self.sample_pixels(image, coordinate_scales=self.coordinate_scales_from(source))


'''
old='''@dataclass(frozen=True, slots=True)
class GranularityImageSeries:
    """Background-corrected image and reconstruction series."""

    pixels: np.ndarray
    new_shape: np.ndarray
    reconstructions: tuple[np.ndarray, ...]
'''
new=old.replace('    new_shape: np.ndarray','    grid: GranularitySamplingGrid');replacements.append((old,new_grid+new))
replacements.append(('from openhcs.processing.backends.cellprofiler._granularity_reconstruct import (\n    reconstruct_f32 as _reconstruct_f32,','from openhcs.processing.backends.cellprofiler._granularity_native import (\n    reconstruct_f32 as _reconstruct_f32,\n    sample_order_one_grid as _sample_order_one_grid,'))
replacements.append(('        pixels, new_shape = background_corrected_pixels(', '        pixels, grid = background_corrected_pixels('))
replacements.append(('            pixels=pixels, new_shape=new_shape, reconstructions=reconstructions','            pixels=pixels, grid=grid, reconstructions=reconstructions'))
a=source.index('def background_corrected_pixels(');b=source.index('\n\ndef granularity_grey_erosion(',a);old=source[a:b]
new='''def background_corrected_pixels(
    image: np.ndarray,
    subsample_size: float,
    background_subsample_size: float,
    element_radius: int,
) -> tuple[np.ndarray, GranularitySamplingGrid]:
    """Return background-subtracted pixels and their owned CP sampling grid."""
    from skimage import morphology

    image = np.asarray(image)
    original_grid = GranularitySamplingGrid(tuple(image.shape))
    if subsample_size < 1:
        grid = original_grid.subsampled(subsample_size)
        scale = 1.0 / float(subsample_size)
        pixels = grid.sample_pixels(image, coordinate_scales=(scale, scale))
    else:
        pixels = image.copy()
        grid = original_grid
    if background_subsample_size < 1:
        background_grid = grid.subsampled(background_subsample_size)
        scale = 1.0 / float(background_subsample_size)
        back_pixels = background_grid.sample_pixels(pixels, coordinate_scales=(scale, scale))
    else:
        back_pixels = pixels.copy()
        background_grid = grid
    footprint = morphology.disk(int(element_radius), dtype=np.uint8)
    back_pixels = granularity_grey_erosion(back_pixels, footprint)
    back_pixels = granularity_grey_dilation(back_pixels, footprint)
    if background_subsample_size < 1:
        back_pixels = grid.sample_grid(back_pixels, background_grid)
    pixels = pixels - back_pixels
    pixels[pixels < 0] = 0
    return pixels, grid
'''
replacements.append((old,new))
a=source.index('class GranularityLabelPixels:');b=source.index('\n\n@njit',a);old=source[a:b];new=old.replace('    object_ids: np.ndarray\n','    grid: GranularitySamplingGrid\n    object_ids: np.ndarray\n',1).replace('        object_ids = np.asarray(object_ids, dtype=np.int32)','        object_ids = np.asarray(object_ids, dtype=np.int32)\n        grid = GranularitySamplingGrid(tuple(label_array.shape))',1).replace('return cls(object_ids, empty, empty, empty, empty, empty)','return cls(grid, object_ids, empty, empty, empty, empty, empty)',1).replace('        return cls(\n            object_ids=object_ids,','        return cls(\n            grid=grid,\n            object_ids=object_ids,',1)
new=new.replace('        logical_shape: np.ndarray,\n        original_shape: tuple[int, int],','        source_grid: GranularitySamplingGrid,').replace('self.resampled_values(image, logical_shape, original_shape)','self.resampled_values(image, source_grid)')
a=new.index('        row_coords = self.row_offsets.astype');b=new.index('        return ndi.map_coordinates',a);new=new[:a]+'''        scales = self.grid.coordinate_scales_from(source_grid)
        row_coords = self.row_offsets.astype(np.float64) * scales[0]
        column_coords = self.column_offsets.astype(np.float64) * scales[1]
'''+new[b:];replacements.append((old,new))
replacements.append(('    orig_shape = image.shape\n    new_shape = series.new_shape\n',''))
replacements.append(('                new_shape,\n                orig_shape,','                series.grid,'))
a=source.index('def resample_to_original_shape_cp(');b=source.index('\n\n@numpy',a);replacements.append((source[a:b]+ '\n\n',''))
replacements.append(('    "GranularityImageSeries",','    "GranularitySamplingGrid",\n    "GranularityImageSeries",'))
changes={str(path):source};operations=[PatchTargetOperation(target=SourceRewriteTarget(file_path=str(path)),replacements=tuple(SourceTextReplacement(old_source=a,new_source=b) for a,b in replacements),rationale='One CP grid owner replaces bare and duplicated shape interpretation. Dense consumers use installed native sampling; sparse consumers derive the same endpoint scales. No old helper aliases or mirrored series shapes. Existing reconstruction family/preparation remains independent.')]
for relative in ('setup.py','tests/unit/test_library_registry_discovery.py','scripts/smoke_native_granularity_wheel.py'):
 p=root/relative;s=p.read_text();changes[str(p)]=s;operations.append(PatchTargetOperation(target=SourceRewriteTarget(file_path=str(p)),replacements=(SourceTextReplacement(old_source=s,new_source=s.replace('_granularity_reconstruct','_granularity_native')),),rationale='Migrate the existing native module declaration and its actual inventory/installed wheel consumers; no stale module alias.'))
p=root/'tests/unit/test_measuregranularity.py';s=p.read_text();changes[str(p)]=s;operations.append(PatchTargetOperation(target=SourceRewriteTarget(file_path=str(p)),replacements=(SourceTextReplacement(old_source=s,new_source=s.replace('series.new_shape','series.grid.logical_shape')),),rationale='The independent sparse-sampling reference derives logical extent from the canonical series grid.'))
recipe=RefactorRecipe(recipe_id='own-granularity-grid-and-installed-native-sampling',operations=tuple(operations),reason='Admitted geometry relation and native cast parity justify one nominal CP grid authority. Exact syntax transaction does not prove numerical behavior; native CPP is authored/compiled separately and all production parity and runtime gates remain open.')
plan=CodemodPlanDocument(recipes=(recipe,));simulation=plan.simulate(CodemodSourceSnapshot.from_source_mapping(changes));assert simulation.is_clean,simulation.simulation_payload()
(root.parent/'openhcs-benchmark-runs/perf-granularity-grid-nra-projected-20260930.diff').write_text(simulation.unified_diff(changes));print(simulation.apply())
