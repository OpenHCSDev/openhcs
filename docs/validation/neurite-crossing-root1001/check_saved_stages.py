"""Engineering comparison of fixed original stages; frozen inputs stay read-only."""
import hashlib
import json
import sys
from pathlib import Path

import numpy as np
import tifffile
from openhcs.processing.backends.analysis import neurite_outgrowth as owner

root = Path('/run/media/ts/hdd/openhcs-science/next-h004-fresh25-89-after-h003-20261006/H004_FRESH25_ROTATION_89')
hashes = {}
witnesses = ((262,379), (230,405), (220,432), (204,452), (182,478))

def read(path):
    hashes[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
    return np.squeeze(tifffile.imread(path))

for attempt in ('attempt04', 'attempt05'):
    base = root / attempt / 'staged-input_openhcs'
    def checkpoint(name):
        return read(base / 'images' / ('PairedField_s001_w1_z001_t001_neurite_' + name + '.checkpoint.tif'))
    candidate = checkpoint('candidate_mask').astype(bool)
    response = checkpoint('local_response')
    secondary = checkpoint('secondary_ownership')
    bodies = read(base / 'results' / 'PairedField_site-1_z_index-1_timepoint-1_cell_bodies_step0.labels.tif')[0]
    skeleton = owner._raw_processing_leaf(owner.medialaxis)(candidate.astype(np.float32)) > 0
    initial = owner._analyze_topology(skeleton, bodies, 1.0, 6.0)
    owned = owner._adopt_secondary_owned_path_segments(
        initial, owner._render_owned_skeleton(candidate.shape, initial), secondary,
    )
    failed_connections = []
    def capture_failed_connection(frame, event, result):
        if event != 'return' or result is not None or frame.f_code is not owner._least_cost_supported_path.__code__:
            return
        parent = frame.f_back.f_locals
        if parent['owner'] != 4:
            return
        origin = np.array([part.start for part in parent['owner_slice']])
        for path_index in initial.root_paths_by_cell.get(4, ()):
            coords = initial.path_coordinates[path_index]
            body_coords = np.argwhere(bodies == 4)
            distances = np.sqrt(np.sum((coords[:,None] - body_coords[None,:])**2,axis=2))
            source_index,body_index = np.unravel_index(np.argmin(distances),distances.shape)
            source_coordinate = coords[source_index]
            failed_connections.append({'root_path':path_index,
                'closest_trace':source_coordinate.tolist(),'closest_body':body_coords[body_index].tolist(),
                'gap':float(distances[source_index,body_index]),
                'trace_secondary':int(secondary[tuple(source_coordinate)])})
        allowed = frame.f_locals['allowed']
        starts = frame.f_locals['starts']
        targets = frame.f_locals['targets']
        components,_ = owner.ndi.label(allowed,structure=np.ones((3,3)))
        roots = np.unique(components[starts & allowed])
        roots = roots[roots > 0]
        for crossing in initial.resolved_crossings:
            if not crossing.supports_owner(4,initial.path_owners):
                continue
            coords = crossing.core_coordinates(initial.path_coordinates)
            local = coords - origin
            inside = np.all((local >= 0) & (local < allowed.shape),axis=1)
            coords,local = coords[inside],local[inside]
            failed_connections.append({'crossing_node':crossing.node,
                'arms':list(crossing.arm_paths),
                'arm_owners':initial.path_owners[list(crossing.arm_paths)].tolist(),
                'core':[{'coordinate':point.tolist(),
                    'input_owner':int(owned[tuple(point)]),
                    'current_owner':int(parent['local_repaired'][tuple(relative)]),
                    'response':float(response[tuple(point)]),
                    'allowed':bool(allowed[tuple(relative)]),
                    'component':int(components[tuple(relative)])}
                    for point,relative in zip(coords,local)]})
        for path_index in (56,60,64,66,68,102,126,128,130,132,134):
            if path_index >= len(initial.path_coordinates):
                continue
            coords = initial.path_coordinates[path_index]
            local = coords - origin
            inside = np.all((local >= 0) & (local < allowed.shape),axis=1)
            coords,local = coords[inside],local[inside]
            blocked = ~allowed[tuple(local.T)]
            failed_connections.append({'chain_path':path_index,
                'logical_owner':int(initial.path_owners[path_index]),
                'component_ids':np.unique(components[tuple(local.T)]).tolist(),
                'blocked': [{'coordinate':point.tolist(),
                    'input_owner':int(owned[tuple(point)]),
                    'current_owner':int(parent['local_repaired'][tuple(relative)]),
                    'body_owner':int(bodies[tuple(point)]),
                    'secondary_owner':int(secondary[tuple(point)]),
                    'response':float(response[tuple(point)])}
                    for point,relative in zip(coords[blocked],local[blocked])]})
        failed_connections.append({'allowed_components':int(components.max()),
                                   'remaining_target_pixels':int(np.count_nonzero(targets)),
                                   'any_target_allowed_root_connection':bool(np.any(targets & np.isin(components,roots))),
                                   'origin':origin.tolist()})
    sys.setprofile(capture_failed_connection)
    repaired = owner._repair_signal_supported_skeleton(
        owned, response, secondary, bodies, minimum_response=3.0,
        crossing_topology=initial,
    )
    sys.setprofile(None)
    print('FAILED_CONNECTIONS',attempt,json.dumps(failed_connections),flush=True)
    crossing = owner._render_crossing_support(candidate.shape, initial)
    core = initial.crossing_core_mask(candidate.shape)
    repaired = np.where(crossing > 0, crossing, repaired).astype(np.int32)
    repaired[bodies > 0] = 0
    final = owner._analyze_owned_topology(repaired, bodies, 1.0, 6.0, crossing_topology=initial)
    rendered = owner._render_owned_skeleton(candidate.shape, final)
    rendered = np.where(core & (crossing > 0), crossing, rendered)
    graph = owner._build_neurite_morphology_graph(
        final, bodies, coordinate_spacing=owner.PixelMetricCoordinates.analysis_spacing(),
        outgrowth_width_px=6.0,
    )
    graph.require_directed_forest()
    neighborhoods = [np.unique(rendered[y-2:y+3,x-2:x+3]).tolist() for y,x in witnesses]
    print(json.dumps({'attempt':attempt,'published_trace_pixels':int(np.count_nonzero(rendered)),
                      'witness_owners':neighborhoods,'graph_edges':len(graph.edges),
                      'coordinate_unit':graph.coordinate_spacing.unit.value}),flush=True)
    assert not failed_connections, f'{attempt}: owner4 still lacks continuous allowed support'
    expected_owner = 6 if attempt == 'attempt04' else 4
    assert all(expected_owner in labels for labels in neighborhoods), (attempt,neighborhoods)
for path, digest in hashes.items():
    assert hashlib.sha256(Path(path).read_bytes()).hexdigest() == digest
print('UNCHANGED_INPUT_HASHES',json.dumps(hashes,sort_keys=True),flush=True)
