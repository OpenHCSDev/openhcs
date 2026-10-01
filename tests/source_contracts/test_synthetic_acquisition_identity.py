"""Tiny producer/metadata controls using real public source imports, no MCP/JVM."""
from contextlib import redirect_stdout
from io import StringIO
import json
from pathlib import Path
import tempfile
import unittest

import tifffile
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
import openhcs.demo.synthetic_data as producer_module
from openhcs.constants.constants import AllComponents
from openhcs.core.source_projection import OpenHCSPlaneAddress
from openhcs.core.virtual_workspace_metadata import (
    FIELDS, VirtualWorkspaceSourceProjectionEntries, component_metadata_field,
    get_metadata_path,
)
from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator
from openhcs.microscopes.microscope_interfaces import FilenameParser
from openhcs.microscopes.openhcs import OpenHCSMetadataHandler
from polystore.virtual_workspace import SourcePixelRef


class SyntheticAcquisitionIdentity(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="synthetic-identity-172-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)

    def generate(self, format, *, z_levels=1, explicit=False, bioformats=False,
                 native=True, wells=("A01",), skip_files=(), grid=(1, 1)):
        plate = self.root / str(len(tuple(self.root.iterdir())))
        with redirect_stdout(StringIO()):
            generator = SyntheticMicroscopyGenerator(
                output_dir=str(plate), format=format, grid_size=grid,
                tile_size=(32, 32), overlap_percent=0, stage_error_px=0,
                wavelengths=2, z_stack_levels=z_levels, num_cells=4,
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
        address_sets = {component: set() for component in AllComponents}
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
            for component in AllComponents:
                address_sets[component].add(projection.address.value_for(component))
        self.assertEqual(len(physical_refs), count)
        for component in AllComponents:
            self.assertEqual(set(metadata[component_metadata_field(component)]), address_sets[component])
        # A fresh real metadata handler reads the persisted component authority.
        reopened = OpenHCSMetadataHandler(
            FileManager({"disk": DiskStorageBackend()})
        ).component_value_set(plate)
        for component in AllComponents:
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
                            self.assertEqual(values[AllComponents.WELL],
                                {"A01", "D12"} if format == "ImageXpress" else {"R01C01", "R04C12"})
                            self.assertEqual(values[AllComponents.SITE], {"1", "2"})
                            self.assertEqual(values[AllComponents.CHANNEL], {"1", "2"})
                            self.assertEqual(values[AllComponents.Z_INDEX], {str(z) for z in range(1, z_levels + 1)})
                            self.assertEqual(values[AllComponents.TIMEPOINT], {"1"})
                            self.assertEqual(metadata[FIELDS.MICROSCOPE_HANDLER_NAME],
                                "imagexpress" if format == "ImageXpress" else "opera_phenix")

    def test_opera_original_well_disagreement_is_not_a_second_inventory_key(self):
        generator, plate = self.generate("OperaPhenix", explicit=True)
        metadata = self.document(plate)
        parser = FilenameParser.__registry__[metadata[FIELDS.SOURCE_FILENAME_PARSER_NAME]]()
        parsed_wells = {parser.parse_filename(path.name).value_for(AllComponents.WELL)
                        for path in plate.rglob("*.tiff")}
        self.assertEqual(set(metadata[FIELDS.WELLS]), parsed_wells)
        self.assertEqual(set(metadata[FIELDS.WELLS]) | parsed_wells, {"R01C01"})
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
        self.assertEqual(values[AllComponents.CHANNEL], {"1"})

    def test_repeat_generation_replaces_emitted_plane_inventory(self):
        generator, plate = self.generate("OperaPhenix", z_levels=2)
        with redirect_stdout(StringIO()):
            generator.generate_dataset()
        self.assert_coherent(plate, self.document(plate), 4)


if __name__ == "__main__":
    unittest.main(verbosity=2)
