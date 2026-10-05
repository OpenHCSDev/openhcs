"""Adapt receiving11's typed VALUES reader and CSV checks for the 743 relation.

Run once after both public jobs are terminal, using their actual VALUES paths
and the execution acquisition root declared by the successful source plan.
No MCP request, source execution, alternative loader or reference data here.
"""

import csv
import hashlib
import json
import math
import sys
from pathlib import Path

target = Path(sys.argv[1]).resolve()
sys.path.insert(0, str(target))
import openhcs
from openhcs.core.runtime_measurements import MeasurementTable
from openhcs.core.source_metadata import SourceMetadataFields
from openhcs.runtime.zmq_execution_observation import ZMQRuntimeExecutionObservationExport
from openhcs.serialization.json import to_jsonable

assert Path(openhcs.__file__).resolve().is_relative_to(target), openhcs.__file__
original_acquisition = Path('/run/media/ts/hdd/openhcs-engineering/engineering721725-public10-94-20261005/photometry722/acquisition')
acquisition = Path(sys.argv[4]).resolve()
output = Path('/run/media/ts/hdd/openhcs-engineering/engineering743-provenance-20261005/public01')
input_hashes = {
    'Mask': 'be5ef4d28ca0cdcad495c89e4006288b88c4dc46e1ce8c301cd19e3ea495bd4c',
    'Process': '860422c6b2230550b06a6a603c341e78137d51761b39b4b899fe67ee09d50484',
    'Nuclear': '1c1c2d03486fcf4643b4379ff98fb4b1c1363053bdef028e09f0f84fc60bf398',
}
for alias, digest in input_hashes.items():
    for root in (original_acquisition, acquisition):
        assert hashlib.sha256((root / f'{alias}.tif').read_bytes()).hexdigest() == digest

numeric_expected = {
    f'Intensity_{feature}_{alias}': expected
    for alias, total, maximum in (('Process', 430, 221 / 255.0), ('Nuclear', 889, 1.0))
    for feature, expected in (('IntegratedIntensity', total / 255.0),
                              ('MeanIntensity', total / (255.0 * 12)),
                              ('MaxIntensity', maximum))
}
orders = {}
receipts = []
for order, values_path in zip(('forward', 'reverse'), sys.argv[2:4], strict=True):
    payload = ZMQRuntimeExecutionObservationExport.read(Path(values_path))
    assert dict(payload.execution_success_by_axis) == {'A01': True}
    measured = []
    sources = {}
    for axis, records in payload.records_by_axis.items():
        assert axis == 'A01', axis
        for record in records:
            table = record.data
            if not isinstance(table, MeasurementTable):
                continue
            provenance = table.source_provenance
            for name in provenance.represented_source_image_names:
                projected = provenance.for_source_image(name)
                previous = sources.setdefault(name, projected)
                assert previous == projected, (order, name)
            if record.key.name == 'TwoImagePhotometry_2_measurements':
                assert table.subject.object_name == 'Cells'
                assert set(provenance.represented_source_image_names) == {'Process', 'Nuclear'}
                assert provenance.source_plane_count == 1
                assert {row['slice_index'] for row in table.rows.iter_row_mappings()} == {0}
                measured.append(table)
    assert len(measured) == 1, (order, len(measured))
    native_rows = tuple(measured[0].rows.iter_row_mappings())
    native_values = {}
    for column, expected in numeric_expected.items():
        values = tuple(row[column] for row in native_rows if column in row)
        assert len(values) == 1, (order, column, values)
        value, = values
        assert math.isclose(float(value), expected, rel_tol=1e-6, abs_tol=1e-6)
        native_values[column] = float(value)
    assert set(sources) == set(input_hashes), (order, sources)
    source_proof = {}
    for name, channel in (('Mask', '1'), ('Process', '2'), ('Nuclear', '3')):
        source = sources[name]
        metadata = dict(source.source_component_metadata or {})
        for key, value in dict(well='A01', site='1', z_index='1', timepoint='1',
                               channel=channel, source_alias=name).items():
            assert metadata[key] == value, (order, name, key, metadata)
        assert metadata['OpenHCSSourceVoxelSpacingUnit'] == 'relative'
        assert metadata['OpenHCSSourceVoxelSpacingZYX'] == '1,1'
        assert str(acquisition / f'{name}.tif') in SourceMetadataFields.source_filter_paths(
            source.source_component_metadata
        ), (order, name, metadata)
        source_proof[name] = dict(path=str(source.source_path), metadata=metadata)

    tables = {}
    for name in ('Image', 'Cells'):
        paths = tuple((output / order).rglob(f'{name}.csv'))
        assert len(paths) == 1, (order, name, paths)
        path, = paths
        with path.open(newline='') as stream:
            rows = tuple(csv.DictReader(stream))
        assert len(rows) == 1, (order, name, rows)
        row, = rows
        for axis, value in dict(well='A01', site='1', z_index='1', timepoint='1').items():
            assert row[f'Metadata_{axis}'] == value, (order, name, axis, row)
        assert row['Metadata_channel'] == '', (order, name, row)
        prefix = 'Image_' if name == 'Cells' else ''
        projected_names = {field.removeprefix(prefix + 'FileName_') for field in row
                           if field.startswith(prefix + 'FileName_')}
        assert projected_names == set(sources), (order, name, projected_names)
        for alias, source in sources.items():
            source_path = Path(source.source_path)
            assert row[f'{prefix}FileName_{alias}'] == source_path.name
            assert row[f'{prefix}PathName_{alias}'] == str(source_path.parent)
        tables[name] = row
        receipts.append(dict(order=order, table=name, path=str(path),
                             sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                             fields=list(row)))
    cell = tables['Cells']
    for column, expected in native_values.items():
        assert math.isclose(float(cell[column]), expected, rel_tol=1e-6, abs_tol=1e-6)
    assert cell['image_number'] == cell['object_label'] == '1'
    orders[order] = dict(csv=tables, native_sources=source_proof)
    receipts.append(dict(order=order, execution_id=payload.execution_id,
                         values_path=values_path,
                         values_sha256=hashlib.sha256(Path(values_path).read_bytes()).hexdigest(),
                         native_sources=source_proof))

assert orders['forward'] == orders['reverse'], 'Input order changed source/numeric identity'
print(json.dumps(to_jsonable(dict(status='PASS', module_origin=openhcs.__file__,
                      loader_origin=sys.modules[ZMQRuntimeExecutionObservationExport.__module__].__file__,
                      original_acquisition=str(original_acquisition),
                      execution_acquisition=str(acquisition), input_hashes=input_hashes,
                      receipts=receipts, values=orders, scientific_data_used=False)), indent=2))
