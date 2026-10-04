"""Reuse the published complete source/dependency parser, without a new scanner."""
from pathlib import Path
import subprocess

checkout = Path(__file__).resolve().parents[2]
path = 'validation/mixed-carrier-intensity-domain-599/source_family.py'
program = subprocess.check_output(['git', '-C', str(checkout), 'show',
    f'c63af64a604df4d940bfa716c6edce565ec82d47:{path}'], text=True)
program = program.replace('"ImagePayloadMetadata", "ImageUnitIntervalIntensityMetadata",',
    '"source_plane_metadata_records", "source_metadata_by_payload", "SourceImageProvenance", "acquisition_tile_positions", "ImagePayloadMetadata", "ImageUnitIntervalIntensityMetadata",')
exec(compile(program, path, 'exec'))
