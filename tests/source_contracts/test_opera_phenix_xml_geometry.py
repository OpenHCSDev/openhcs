"""Pure XML contracts, runnable without microscope discovery or science runtimes.

Load the actual parser source file, not a replacement package or patched parser.
Normal public-package discovery/installed acceptance belongs to integration.
"""

import importlib.util
from pathlib import Path
import tempfile
import unittest
import xml.etree.ElementTree as ET


SOURCE = Path(__file__).resolve().parents[2] / "openhcs/microscopes/opera_phenix_xml_parser.py"
SPEC = importlib.util.spec_from_file_location("opera_xml_geometry_source", SOURCE)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)
Parser = MODULE.OperaPhenixXmlParser
ContentError = MODULE.OperaPhenixXmlContentError
NAMESPACE = "http://www.perkinelmer.com/PEHH/HarmonyV6"


def image(parent, *, well=(1, 1), channel=1, plane=1, field=1, position=(0.0, 0.0)):
    element = ET.SubElement(parent, "Image", Version="1")
    for tag, value in (
        ("Row", well[0]), ("Col", well[1]), ("ChannelID", channel),
        ("PlaneID", plane), ("FieldID", field),
        ("PositionX", position[0]), ("PositionY", position[1]),
    ):
        ET.SubElement(element, tag).text = str(value)
    return element


class OperaXmlGeometryContract(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="opera-xml-172-")
        self.addCleanup(self.directory.cleanup)

    def parser(self, root):
        path = Path(self.directory.name) / "Index.xml"
        ET.ElementTree(root).write(path, encoding="utf-8", xml_declaration=True)
        return Parser(path)

    def test_source_identity(self):
        self.assertEqual(Path(MODULE.__file__).resolve(), SOURCE.resolve())
        self.assertEqual(Parser.__module__, SPEC.name)

    def test_singleton_and_colocated_channel_plane_fields(self):
        for namespace in ("", NAMESPACE):
            for channels, planes in ((1, 1), (3, 1), (1, 3), (3, 3)):
                with self.subTest(namespace=namespace, channels=channels, planes=planes):
                    root = ET.Element("EvaluationInputData", xmlns=namespace)
                    for channel in range(1, channels + 1):
                        for plane in range(1, planes + 1):
                            image(root, channel=channel, plane=plane,
                                  field=17, position=(0.000576762, 0.000576762))
                    parser = self.parser(root)
                    self.assertEqual(parser.get_grid_size(), (1, 1))
                    self.assertEqual(parser.get_field_id_mapping(), {17: 1})

    def test_rectangular_stage_geometry_and_raster_mapping(self):
        for rows, cols in ((1, 4), (4, 1), (2, 3), (3, 2), (3, 3)):
            with self.subTest(rows=rows, cols=cols):
                root = ET.Element("EvaluationInputData", xmlns=NAMESPACE)
                # Non-contiguous, reversed field IDs: IDs do not define geometry.
                positions = {}
                expected_mapping = {}
                for row in range(rows):
                    for col in range(cols):
                        field = 17 + 2 * (rows * cols - (row * cols + col))
                        position = (0.000576762 + col * 0.001,
                                    0.000576762 + (rows - row - 1) * 0.001)
                        positions[field] = position
                        expected_mapping[field] = row * cols + col + 1
                        for channel in (1, 2):
                            for plane in (1, 2):
                                image(root, field=field, position=position,
                                      channel=channel, plane=plane)
                parser = self.parser(root)
                self.assertEqual(parser.get_grid_size(), (cols, rows))
                self.assertEqual(parser.get_field_positions(), positions)
                self.assertEqual(parser.get_field_id_mapping(), expected_mapping)

    def test_positions_are_scoped_to_one_well_channel_plane(self):
        root = ET.Element("EvaluationInputData")
        for well, channel, plane, offset in (
            ((1, 1), 1, 1, 0), ((1, 2), 1, 1, 10),
            ((1, 1), 2, 1, 20), ((1, 1), 1, 2, 30),
        ):
            for field in range(1, 4):
                image(root, well=well, channel=channel, plane=plane,
                      field=field, position=(offset + field * 0.001, offset))
        self.assertEqual(self.parser(root).get_grid_size(), (3, 1))

    def test_coordinate_quantization_is_preserved(self):
        root = ET.Element("EvaluationInputData")
        image(root, field=1, position=(0, 0))
        image(root, field=2, position=(0.001, 1e-12))
        image(root, field=3, position=(1e-12, 0.001))
        image(root, field=4, position=(0.001, 0.001))
        self.assertEqual(self.parser(root).get_grid_size(), (2, 2))

    def test_partial_singleton_does_not_displace_first_multifield_group(self):
        root = ET.Element("EvaluationInputData")
        image(root, well=(1, 1))
        for field in range(1, 4):
            image(root, well=(1, 2), field=field, position=(field * 0.001, 0))
        for field in range(1, 5):
            image(root, well=(1, 3), field=field, position=(0, field * 0.001))
        self.assertEqual(self.parser(root).get_grid_size(), (3, 1))

    def test_numeric_group_identity_merges_external_padding_not_channels(self):
        root = ET.Element("EvaluationInputData")
        first = image(root, field=17, position=(0, 0))
        first.find("Row").text = "01"
        first.find("Col").text = "01"
        image(root, field=19, position=(0.001, 0))
        image(root, channel=2, field=17, position=(10, 10))
        self.assertEqual(self.parser(root).get_grid_size(), (2, 1))

    def test_invalid_coordinates_do_not_become_a_guessed_grid(self):
        for bad in ("not-a-number", "nan", "inf", "-inf", ""):
            with self.subTest(bad=bad):
                root = ET.Element("EvaluationInputData")
                image(root, position=(bad, 0), field=16)
                parser = self.parser(root)
                with self.assertRaisesRegex(ContentError, "Could not determine grid size from XML data"):
                    parser.get_grid_size()
                self.assertEqual(parser.get_field_positions(), {})

    def test_missing_coordinate_does_not_mask_later_valid_group(self):
        root = ET.Element("EvaluationInputData")
        invalid = image(root, channel=1)
        invalid.remove(invalid.find("PositionX"))
        image(root, channel=2, field=17)
        self.assertEqual(self.parser(root).get_grid_size(), (1, 1))

    def test_empty_or_reference_only_images_preserve_content_errors(self):
        for references in (False, True):
            with self.subTest(references=references):
                root = ET.Element("EvaluationInputData")
                if references:
                    ET.SubElement(root, "Image", id="0101K1F1P1R1")
                with self.assertRaises(ContentError):
                    self.parser(root).get_grid_size()

    def test_remapping_position_reader_does_not_require_grid_group_tags(self):
        root = ET.Element("EvaluationInputData")
        field = image(root, field=17)
        for tag in ("Row", "Col", "ChannelID", "PlaneID"):
            field.remove(field.find(tag))
        parser = self.parser(root)
        self.assertEqual(parser.get_field_positions(), {17: (0, 0)})
        with self.assertRaises(ContentError):
            parser.get_grid_size()


if __name__ == "__main__":
    unittest.main(verbosity=2)
