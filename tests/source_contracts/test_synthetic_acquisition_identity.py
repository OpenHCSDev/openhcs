"""Tiny producer/metadata controls using real public source imports, no MCP/JVM."""
from contextlib import redirect_stdout
from io import StringIO
import json
from pathlib import Path
import tempfile
import unittest
import xml.etree.ElementTree as ET

import numpy as np
import tifffile
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
import openhcs.demo.synthetic_data as producer_module
from openhcs.core.source_projection import (
    OpenHCSPlaneAddress, SourcePlaneProjection, SourceProjectionSet,
    SourceProjectionMetadataSerializer,
)
from openhcs.core.components.parser_metaprogramming import GenericFilenameParser
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.virtual_workspace_metadata import (
    FIELDS, VirtualWorkspaceSourceProjectionEntries,
    AtomicMetadataWriter, get_metadata_path,
)
from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator
from openhcs.core.dataset_sources.interfaces import FilenameParser
from openhcs.core.dataset_sources.openhcs_format import OpenHCSMetadataHandler
from openhcs.microscopes.imagexpress import ImageXpressFilenameParser, ImageXpressHandler
from openhcs.core.dataset_sources.source import DatasetSource
from polystore.virtual_workspace import SourcePixelRef
from openhcs.core.axes import AxisFamily
from openhcs.domains.microscopy.axes import Microscopy


class SyntheticAcquisitionIdentity(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="synthetic-identity-172-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)

    def generate(self, format, *, z_levels=1, explicit=False, bioformats=False,
                 native=True, wells=("A01",), skip_files=(), grid=(1, 1), channels=2):
        plate = self.root / str(len(tuple(self.root.iterdir())))
        with redirect_stdout(StringIO()):
            generator = SyntheticMicroscopyGenerator(
                output_dir=str(plate), format=format, grid_size=grid,
                tile_size=(32, 32), overlap_percent=0, stage_error_px=0,
                wavelengths=channels, z_stack_levels=z_levels, num_cells=4,
                wells=list(wells), random_seed=7, include_all_components=explicit,
                imagexpress_bioformats_compatible=bioformats,
                openhcs_format=native, skip_files=list(skip_files),
            )
            generator.generate_dataset()
        return generator, plate

    def document(self, plate, subdirectory=None):
        document = json.loads(get_metadata_path(plate).read_text())
        entries = document[FIELDS.SUBDIRECTORIES]
        return entries[subdirectory] if subdirectory else next(iter(entries.values()))

    def assert_coherent(self, plate, metadata, count):
        paths = metadata[FIELDS.IMAGE_FILES]
        self.assertEqual(len(paths), count)
        self.assertEqual(len(set(paths)), count)
        projections = VirtualWorkspaceSourceProjectionEntries.from_subdirectory(metadata).entries
        self.assertEqual(set(projections), set(paths))
        self.assertEqual(set(metadata[FIELDS.WORKSPACE_MAPPING]), set(paths))
        parser = FilenameParser.__registry__[metadata[FIELDS.SOURCE_FILENAME_PARSER_NAME]]()
        address_sets = {component: set() for component in AxisFamily.active().axes}
        physical_refs = set()
        for path, projection in projections.items():
            parsed = parser.parse_filename(Path(path).name)
            self.assertIsNotNone(parsed)
            self.assertEqual(OpenHCSPlaneAddress.from_component_values(parsed.declared_values()), projection.address)
            ref = SourcePixelRef.from_workspace_mapping(metadata[FIELDS.WORKSPACE_MAPPING][path])
            self.assertEqual(ref, projection.ref)
            self.assertEqual(ref.backend, "disk")
            physical = plate / ref.backend_address
            self.assertTrue(physical.is_file())
            self.assertEqual(tifffile.imread(physical).shape, (32, 32))
            physical_refs.add(ref.backend_address)
            for component in AxisFamily.active().axes:
                address_sets[component].add(projection.address.value_for(component))
        self.assertEqual(len(physical_refs), count)
        for component in AxisFamily.active().axes:
            self.assertEqual(set(metadata[component.metadata_collection_field]), address_sets[component])
        # A fresh real metadata handler reads the persisted component authority.
        reopened = OpenHCSMetadataHandler(
            FileManager({"disk": DiskStorageBackend()})
        ).component_value_set(plate)
        for component in AxisFamily.active().axes:
            self.assertEqual(set(reopened.values_for(component)), address_sets[component])
        return address_sets

    def test_source_identity(self):
        expected = Path(__file__).resolve().parents[2] / "openhcs/demo/synthetic_data.py"
        self.assertEqual(Path(producer_module.__file__).resolve(), expected)

    def test_raw_and_native_family_all_components_and_exact_source_refs(self):
        for format in ("ImageXpress", "OperaPhenix"):
            for z_levels in (1, 2):
                for explicit in (False, True):
                    for native in (False, True):
                        with self.subTest(format=format, z_levels=z_levels, explicit=explicit, native=native):
                            generator, plate = self.generate(format, z_levels=z_levels,
                                explicit=explicit, native=native, wells=("A01", "D12"), grid=(1, 2))
                            if not native:
                                self.assertFalse(get_metadata_path(plate).exists())
                                with redirect_stdout(StringIO()):
                                    generator.generate_openhcs_metadata(sub_dir="custom")
                            metadata = self.document(plate)
                            values = self.assert_coherent(plate, metadata, 8 * z_levels)
                            self.assertEqual(values[Microscopy.Well],
                                {"A01", "D12"} if format == "ImageXpress" else {"R01C01", "R04C12"})
                            self.assertEqual(values[Microscopy.Site], {"1", "2"})
                            self.assertEqual(values[Microscopy.Channel], {"1", "2"})
                            self.assertEqual(values[Microscopy.ZIndex], {str(z) for z in range(1, z_levels + 1)})
                            self.assertEqual(values[Microscopy.Timepoint], {"1"})
                            self.assertEqual(metadata[FIELDS.MICROSCOPE_HANDLER_NAME],
                                "imagexpress" if format == "ImageXpress" else "opera_phenix")

    def test_opera_original_well_disagreement_is_not_a_second_inventory_key(self):
        generator, plate = self.generate("OperaPhenix", explicit=True)
        metadata = self.document(plate)
        parser = FilenameParser.__registry__[metadata[FIELDS.SOURCE_FILENAME_PARSER_NAME]]()
        parsed_wells = {parser.parse_filename(path.name).value_for(Microscopy.Well)
                        for path in plate.rglob("*.tiff")}
        self.assertEqual(set(metadata[Microscopy.Well.metadata_collection_field]), parsed_wells)
        self.assertEqual(set(metadata[Microscopy.Well.metadata_collection_field]) | parsed_wells, {"R01C01"})
        self.assert_coherent(plate, metadata, 2)

    def test_imagexpress_bioformats_stack_retains_folder_axis_and_refs(self):
        generator, plate = self.generate("ImageXpress", z_levels=2, bioformats=True,
                                        wells=("A01",), grid=(1, 2))
        metadata = self.document(plate)
        self.assert_coherent(plate, metadata, 8)
        physical = {projection.ref.backend_address for projection in
                    VirtualWorkspaceSourceProjectionEntries.from_subdirectory(metadata).entries.values()}
        self.assertEqual({Path(path).parent.name for path in physical}, {"ZStep_1", "ZStep_2"})

    def test_skipped_plane_cannot_leave_phantom_catalog_or_reference(self):
        generator, plate = self.generate("OperaPhenix", skip_files=("r01c01f1p01-ch2sk1fk1fl1.tiff",))
        metadata = self.document(plate)
        values = self.assert_coherent(plate, metadata, 1)
        self.assertEqual(values[Microscopy.Channel], {"1"})

    def test_repeat_generation_replaces_emitted_plane_inventory(self):
        generator, plate = self.generate("OperaPhenix", z_levels=2)
        with redirect_stdout(StringIO()):
            generator.generate_dataset()
        self.assert_coherent(plate, self.document(plate), 4)

    def test_sparse_sites_are_derived_from_saved_planes(self):
        skipped = tuple(f"r01c01f{site}p01-ch{channel}sk1fk1fl1.tiff"
                        for site in (1, 3) for channel in (1, 2))
        generator, plate = self.generate("OperaPhenix", grid=(1, 4), skip_files=skipped)
        values = self.assert_coherent(plate, self.document(plate), 4)
        self.assertEqual(values[Microscopy.Site], {"2", "4"})

    def test_new_complete_address_needs_no_metadata_variant(self):
        generator, plate = self.generate("OperaPhenix")
        with redirect_stdout(StringIO()):
            generator._write_plane(np.full((32, 32), 172, dtype=np.uint16),
                                   plate / "Images", "D12", 17, 7, 99)
            generator.generate_openhcs_metadata(sub_dir="Images")
        values = self.assert_coherent(plate, self.document(plate), 3)
        self.assertEqual(values[Microscopy.Well], {"R01C01", "R04C12"})
        self.assertEqual(values[Microscopy.ZIndex], {"1", "99"})
        self.assertEqual(values[Microscopy.Site], {"1", "17"})
        self.assertEqual(values[Microscopy.Channel], {"1", "2", "7"})
        np.testing.assert_array_equal(tifffile.imread(plate / "Images/r04c12f17p99-ch7sk1fk1fl1.tiff"),
                                      np.full((32, 32), 172, dtype=np.uint16))

    def test_bioformats_scalar_tokens_can_be_absent_without_losing_identity(self):
        generator, plate = self.generate("ImageXpress", channels=1, bioformats=True)
        self.assertEqual({path.name for path in plate.rglob("*.tif")}, {f"{plate.name}_A01.tif"})
        values = self.assert_coherent(plate, self.document(plate), 1)
        for component in AxisFamily.active().axes:
            if component is not Microscopy.Well:
                self.assertEqual(values[component], {"1"})

    def test_xml_urls_and_physical_names_share_parser_owner(self):
        generator, plate = self.generate("OperaPhenix", z_levels=2,
                                        wells=("A01", "D12"), grid=(2, 2))
        root = ET.parse(plate / "Images/Index.xml").getroot()
        urls = {element.text for element in root.iter() if element.tag.endswith("}URL")}
        self.assertEqual(urls, {path.name for path in plate.rglob("*.tiff")})
        self.assert_coherent(plate, self.document(plate), 32)

    def test_nominal_acquisition_operation_respects_existing_mro(self):
        generator, plate = self.generate("OperaPhenix")
        parser = generator.parser
        self.assertIsInstance(parser, GenericFilenameParser)
        components = generator._plane_components("D12", 17, 7, 99)
        canonical = GenericFilenameParser.construct_acquisition_filename(parser, components)
        self.assertEqual(canonical, parser.construct_filename(components))
        self.assertEqual(parser.construct_acquisition_filename(components),
                         "r04c12f17p99-ch7sk1fk1fl1.tiff")

    def test_raw_native_acquisition_calibration_and_source_units_are_identical(self):
        for format in ("ImageXpress", "OperaPhenix"):
            for z_levels in (1, 2):
                with self.subTest(format=format, z_levels=z_levels):
                    raw_generator, raw_plate = self.generate(format, native=False, z_levels=z_levels)
                    native_generator, native_plate = self.generate(format, native=True, z_levels=z_levels)
                    acquisition = type(raw_generator.microscope_handler)(
                        FileManager({"disk": DiskStorageBackend()})).metadata_handler
                    raw_spacing = acquisition.source_voxel_spacing(raw_plate)
                    native_reader = OpenHCSMetadataHandler(FileManager({"disk": DiskStorageBackend()}))
                    self.assertEqual(native_reader.source_voxel_spacing(native_plate), raw_spacing)
                    self.assertEqual(native_reader.get_pixel_size(native_plate), acquisition.get_pixel_size(raw_plate))
                    projections = VirtualWorkspaceSourceProjectionEntries.from_subdirectory(
                        self.document(native_plate)).entries
                    for projection in projections.values():
                        self.assertEqual(SourceVoxelSpacing.from_source_metadata(projection.source_metadata), raw_spacing)
                    raw_files = {path.relative_to(raw_plate) for path in raw_plate.rglob("*.tif*")}
                    native_files = {path.relative_to(native_plate) for path in native_plate.rglob("*.tif*")}
                    self.assertEqual(raw_files, native_files)
                    for path in raw_files:
                        np.testing.assert_array_equal(tifffile.imread(raw_plate / path),
                                                      tifffile.imread(native_plate / path))

    def test_absent_acquisition_cannot_publish_default_physical_calibration(self):
        generator, plate = self.generate("OperaPhenix", native=False)
        # Only this new disposable control's XML is removed. Historical and
        # frozen fixtures are not inputs to this negative admission test.
        (plate / "Images/Index.xml").unlink()
        with self.assertRaises(FileNotFoundError), redirect_stdout(StringIO()):
            generator.generate_openhcs_metadata(sub_dir="Images")
        self.assertFalse(get_metadata_path(plate).exists())

    def test_new_nominal_capabilities_cooperate_through_real_parser_diamond(self):
        # Independent behaviors, not sibling format implementations: one records
        # physical acquisitions; the other scopes their names. Both cooperate
        # through the real owning ABC and the existing ImageXpress leaf.
        class RecordedAcquisition(GenericFilenameParser):
            def __init__(self, *args, **kwargs):
                self.acquisition_calls = []
                super().__init__(*args, **kwargs)

            def construct_acquisition_filename(self, components, **options):
                name = super().construct_acquisition_filename(components, **options)
                self.acquisition_calls.append(name)
                return name

        class ScopedAcquisition(GenericFilenameParser):
            def construct_acquisition_filename(self, components, **options):
                return "scope172_" + super().construct_acquisition_filename(components, **options)

        class RecordedScopedImageXpressParser(
            RecordedAcquisition, ScopedAcquisition, ImageXpressFilenameParser
        ):
            pass

        class ScopedRecordedImageXpressParser(
            ScopedAcquisition, RecordedAcquisition, ImageXpressFilenameParser
        ):
            pass

        for parser_type in (RecordedScopedImageXpressParser, ScopedRecordedImageXpressParser):
            with self.subTest(parser_type=parser_type.__name__):
                parser = parser_type()
                self.assertIs(FilenameParser.__registry__[parser_type.__name__], parser_type)
                self.assertEqual(parser_type.__mro__.count(GenericFilenameParser), 1)
                self.assertEqual(parser.FILENAME_COMPONENTS, AxisFamily.active().axes)
                components = parser.bind_declared_values(
                    ((Microscopy.Well, "D12"), (Microscopy.Site, 17),
                     (Microscopy.Channel, 7), (Microscopy.ZIndex, 99),
                     (Microscopy.Timepoint, 3)))
                physical_name = parser.construct_acquisition_filename(components)
                self.assertEqual(physical_name, "scope172_D12_s017_w7.tif")
                self.assertEqual(len(parser.acquisition_calls), 1)
                expected_record = (physical_name if parser_type is RecordedScopedImageXpressParser
                                   else "D12_s017_w7.tif")
                self.assertEqual(parser.acquisition_calls, [expected_record])
                # The ancestor's canonical operation still carries every axis.
                canonical = GenericFilenameParser.construct_acquisition_filename(parser, components)
                self.assertEqual(canonical, "D12_s017_w7_z099_t003.tif")
                plate = self.root / parser_type.__name__
                plate.mkdir()
                tifffile.imwrite(plate / physical_name, np.full((32, 32), 172, dtype=np.uint16))
                projection = SourcePlaneProjection(
                    OpenHCSPlaneAddress.from_component_values(components.declared_values()),
                    SourcePixelRef("disk", physical_name),
                )
                # Real unchanged consumer and automatic declaration registry:
                # no alternate formatter, registration edits or reader adapter.
                metadata = SourceProjectionMetadataSerializer(parser).metadata_dict(
                    SourceProjectionSet((projection,)), microscope_handler_name="imagexpress",
                    source_filename_parser_name=parser_type.__name__,
                    grid_dimensions=[1, 1], pixel_size=0.65, main=True)
                AtomicMetadataWriter().replace_subdirectory_metadata(get_metadata_path(plate), ".", metadata)
                values = self.assert_coherent(plate, metadata, 1)
                self.assertEqual(values[Microscopy.ZIndex], {"99"})
                self.assertEqual(values[Microscopy.Timepoint], {"3"})

        class RecordedScopedImageXpressHandler(ImageXpressHandler):
            source_name = "recorded_scoped_imagexpress"

            def __init__(self, filemanager, pattern_format=None):
                super().__init__(filemanager, pattern_format)
                self.parser = RecordedScopedImageXpressParser(filemanager, pattern_format)

        self.assertIs(DatasetSource.__registry__[RecordedScopedImageXpressHandler.source_name],
                      RecordedScopedImageXpressHandler)
        plate = self.root / "declared-producer-extension"
        with redirect_stdout(StringIO()):
            generator = SyntheticMicroscopyGenerator(
                str(plate), format="RecordedScopedImageXpress", grid_size=(1, 1),
                tile_size=(32, 32), wavelengths=1, num_cells=4, wells=["D12"],
                overlap_percent=0, stage_error_px=0, random_seed=7)
            generator.generate_htd_file()
            # Plane emission and metadata are the assigned identity surface;
            # this does not certify new-family HTD/grid-layout generation.
            generator._write_plane(np.full((32, 32), 172, dtype=np.uint16),
                                   generator.timepoint_dir, "D12", 17, 7, 99)
            generator.generate_openhcs_metadata(sub_dir=generator.timepoint_dir.name)
        self.assertIsInstance(generator.parser, RecordedScopedImageXpressParser)
        self.assertEqual(generator.parser.acquisition_calls, ["scope172_D12_s017_w7.tif"])
        self.assert_coherent(plate, self.document(plate), 1)


if __name__ == "__main__":
    unittest.main(verbosity=2)
