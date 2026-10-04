"""Replay a retained eight-well batch with long versus projected wide rows.

Pass the saved RuntimeArtifactBatch pickle path as the first argument.
The pivot is outside the measured interval; production emits wide columns directly.
"""

import hashlib
import pickle
import sys
import time
from dataclasses import replace
from types import MappingProxyType

import numpy as np

from openhcs.core.measurement_row_materialization import (
    MeasurementProjectedColumnarRows,
    WideMeasurementRowAccumulator,
)
from openhcs.core.runtime_tabular_values import FieldSpec
from openhcs.processing.backends.cellprofiler import spreadsheet_export as export

source = sys.argv[1]
with open(source, "rb") as stream:
    batch = pickle.load(stream)

started = time.perf_counter()
record_count = source_row_count = wide_row_count = 0
by_axis = {}
for axis, records in batch.records_by_axis.items():
    replacements = []
    for record in records:
        if not record.key.name.startswith("MeasureObjectIntensityDistribution"):
            replacements.append(record)
            continue
        table = record.value.data
        accumulator = WideMeasurementRowAccumulator(
            export.CELLPROFILER_MEASUREMENT_DIALECT.row_identity_contract
        )
        accumulator.add(
            table.rows,
            export.CELLPROFILER_MEASUREMENT_DIALECT.projected_feature_name,
            default_subject=export._measurement_subject_name(table),
            default_scope=table.subject.scope,
            source_image_name=table.source_image_name,
            object_id_field=table.subject.object_id_field,
            qualifier_field_names=export.measurement_qualifier_field_names(
                export.CELLPROFILER_MEASUREMENT_DIALECT
            ),
        )
        mappings = accumulator.row_mappings_by_subject()[
            export._measurement_subject_name(table)
        ]
        columns = tuple(dict.fromkeys(key for row in mappings for key in row))
        wide = MeasurementProjectedColumnarRows(
            MappingProxyType(
                {name: np.asarray([row[name] for row in mappings]) for name in columns}
            ),
            fields=tuple(
                FieldSpec(
                    name, int if name in ("slice_index", "object_label") else float
                )
                for name in columns
            ),
            declared_object_measurement_domain_covered=table.rows.covers_declared_object_measurement_domain,
            object_row_identity=table.rows.object_row_identity,
        )
        candidate_table = replace(table, rows=wide)
        replacements.append(
            replace(record, value=replace(record.value, data=candidate_table))
        )
        record_count += 1
        source_row_count += table.rows.row_count()
        wide_row_count += wide.row_count()
    by_axis[axis] = tuple(replacements)
candidate = replace(batch, records_by_axis=by_axis)
print(
    "prototype_build",
    time.perf_counter() - started,
    "records",
    record_count,
    "long_rows",
    source_row_count,
    "wide_rows",
    wide_row_count,
    flush=True,
)

kwargs = {
    "export_all_measurement_types": False,
    "file_selections": (
        export.SpreadsheetFileSelection(
            ("BF_cells_on_grid", "SSC"), "BF_cells_on_grid.csv"
        ),
    ),
    "add_filename_prefix": False,
}
payloads = []
for name, selected in (("control", batch), ("wide", candidate)):
    started = time.perf_counter()
    bundle = export.render_spreadsheet_bundle(selected, **kwargs)
    seconds = time.perf_counter() - started
    payload = bundle["BF_cells_on_grid.csv"].encode()
    payloads.append(payload)
    print(
        name,
        "render",
        seconds,
        "bytes",
        len(payload),
        "sha256",
        hashlib.sha256(payload).hexdigest(),
        flush=True,
    )
    started = time.perf_counter()
    serialized = pickle.dumps(selected, protocol=pickle.HIGHEST_PROTOCOL)
    print(
        name,
        "pickle_seconds",
        time.perf_counter() - started,
        "pickle_bytes",
        len(serialized),
        flush=True,
    )

assert payloads[0] == payloads[1], "Wide projection changed spreadsheet bytes"
