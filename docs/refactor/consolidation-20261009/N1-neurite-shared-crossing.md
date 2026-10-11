# N1: Neurite shared crossing

**Head audited:** `openhcs` `main` at `eb64b3c13` (#1202). **Rules:** [00-RULES.md](00-RULES.md). **Origin:** fork (crossing resolution added in `4b4f6e611`).
**Owner decision (2026-10-11):** where two neurons' neurites cross, the graph lets both neurons' paths pass through the same crossing pixel.
**Scope:** `openhcs/processing/backends/analysis/neurite_outgrowth.py` and its tests only.

## What is wrong

**A resolved crossing is declared once (`_ResolvedCrossing`), but the final topology lends each owner only the raster core of the crossing. Each neuron's path therefore detours around the true crossing point, and the measurements are biased: +2√2−2 ≈ 0.83 px of length per crossing and lower straightness for both neurons.**

Measured at `eb64b3c13`:

- Medial-axis thinning of two crossing shafts leaves a hollow diamond, or a 2×2 block for even-parity diagonals, instead of a crossing pixel. Skan's core path runs along one diagonal of that diamond (`(63,75)→(64,74)` in the synthetic case).
- `_analyze_owned_topology` (`neurite_outgrowth.py:2990`) adds `crossing_support_mask` (the core pixels) to each owner's raster. So each owner's path runs arm → diamond corner → arm. In `test_filled_two_neuron_crossing_keeps_the_same_owners_as_final_traces`, each neuron measures 83.83 px with straightness 0.990, against 83.00 px and 1.000 for the same neuron drawn alone. The test itself failed on `main` (the crossing pixel was 0 in the trace image).
- A crossing whose arms meet in one Skan node has no core path. Its core mask is empty, so:
  - `_count_multi_owner_crossings` (`:3678`, raster adjacency) reports 0 crossovers;
  - in the diagonal family case the second neuron loses its distal half (52.3 px instead of 117.4 px).
- `analyze` overwrites the trace image with a nearest-owner core raster (`:466-475`), a second rendering of the crossing beside the topology.
- Mean outgrowth intensity reads the one-label-per-pixel expanded image, so a crossing's signal counts for one neuron only.
- Crossing pairing reads arm directions from the node to the `lookahead` pixel (`_crossing_pairs`, `:3159`). That span is the one the crossing distorts. A single neuron whose two daughters leave one shaft point at 60° on opposite sides was paired as a crossing, and the daughters lost ownership (branch investigation; 435 µm traced versus 654 µm with a 4 px offset).

`docs/validation/neurite-crossing-root1001/OWNER-CHECKPOINT.rst` no longer exists at this head: D5 (`aff991a60`) deleted it as uncited. Its acceptance list is restated under Tests below, with this decision added.

## Target

- **`_ResolvedCrossing` stays the one declaration.** Its arms become `(path, endpoint)` pairs (`arms`), so the side of each arm that touches the core is declared, not inferred; `arm_paths` is derived. `passages()` derives:
  - the replaced span: the core plus each arm's first `lookahead` pixels;
  - the crossing pixel: the pixel near the core through which the owners' 8-connected passages are shortest;
  - each owner's outer arm pixels.
  `shifted()` replaces the hand-written re-indexing in `_analyze_owned_topology`.
- **`_TopologyResult.crossing_routes`** gives each owner a route: digital straight lines from each surviving arm (its outer pixel still carries the owner after repair) to the shared crossing pixel. The final per-owner analysis replaces the distorted span with that route. Both neurons' paths then traverse the crossing pixel, and Skan measures each as if the other neurite were absent. `crossing_lookahead` is declared once and used by both pairing and routing.
- **Derived views.** Each of these is derived from the topology:
  - `multi_owner_crossing_count` (crossings whose crossover arms belong to ≥2 neurons) replaces `_count_multi_owner_crossings`;
  - `shared_trace_owners()` lists the trace pixels that several owners' paths traverse;
  - the trace image is rendered from the topology alone. A shared pixel shows the lowest owner label, a rule documented on `_render_owned_skeleton`. The nearest-owner core overwrite is deleted.
- **Intensity.** Outgrowth pixels whose nearest trace pixel is shared count for every owner whose path traverses it. This uses `shared_trace_owners()`, not the rendered image.
- **Pairing reads directions beyond the distorted span:** pixel `L` to pixel `2L` from the node. 60° same-point bifurcations are then no longer crossings.
- **Topology-class plane** (coordinator request). `NeuriteTopologyClass` is an `AutoRegisterMeta` family keyed by `plane_value`. Each class owns its value and the pixels it marks: none 0, path 1, endpoint 2, soma attachment 3, branch point 4, crossing 5. `value_table()` and `render()` derive from the registry, and higher values paint last. The plane is the `topology_class` field of `NeuriteOwnershipPlanes`, so the checkpoint output, the runtime tuple and the artifact spec all derive from that field. Owner label images keep neuron IDs only.

Deleted:
- `_count_multi_owner_crossings`;
- the `crossing_core_support` overwrite in `analyze`;
- `_crossing_pairs`' node-anchored direction sample;
- the per-field `_ResolvedCrossing` re-indexing in `_analyze_owned_topology`;
- the `lookahead` formula restated in `_analyze_topology`.

## Guards

`tests/unit/test_n1_neurite_crossing_guards.py`:
- `_analyze_owned_topology` calls `crossing_routes`, never `crossing_support_mask`;
- `_count_multi_owner_crossings` and `crossing_core_support` do not exist in the module;
- the topology-class value table equals the registry, and a new class registers with one declaration (new-case test).

## Tests

- `test_crossing_neurons_measure_as_if_drawn_alone` is one family test over four scenes: orthogonal, diagonal, one neurite crossing two others, and a crossing 4 px from a branch point. For every crossing neuron, total_outgrowth must equal its drawn-alone counterpart within √2 (one pixel step), and then exactly. Straightness must also be exact, and processes and branches equal. The test also checks:
  - `resolved_crossovers`;
  - that every crossing-class pixel lies on the graph edges of ≥2 owners and shows the lowest owner in the trace image;
  - that no branch-point class sits within 2 px of a crossing, and that a real branch point is classed as one.
- `test_crossing_signal_counts_for_every_neuron_passing_through_it`: both neurons' mean outgrowth intensity includes a bright crossing pixel and equals their drawn-alone values. It fails when shared counting is disabled.
- `test_single_neuron_bifurcation_is_not_a_crossing`:
  - T (3 arms): branch point, daughters owned;
  - 60° same-point split: no crossing, daughters owned.
- `test_collinear_opposite_daughters_stay_an_unowned_crossing` records the open decision below.
- Kept from the `4b4f6e611` acceptance list, all passing:
  - curved-support and foreign-owner negatives;
  - resolved single-owner and multi-owner crossings with attached distal paths, including reversed owner order, foreign input 99, the below-threshold core, and the 8 MP regional projection;
  - no synthetic owner restoration;
  - branch arms in the shared declaration.
  `test_short_two_junction_crossing_resolves_opposite_rooted_traces` now asserts ownership outside the replaced span, and that both owners share one crossing pixel.
- **New acceptance entry (2026-10-11):** a resolved crossing is traversed by every owner whose arms enter it. Lengths, straightness, process lengths and branches equal the no-crossing case. The label image shows the lowest owner, and measurements never read that choice.

## Open decision (default kept)

| ID | Question | Default |
|---|---|---|
| N1-Q1 | A shaft whose two daughters leave one point collinearly on opposite sides (a `+`) is the same image as an unrooted neurite crossing the shaft (`test_unrooted_crossing_arm_is_not_reported_as_a_branch` draws a `+`). Treat it as a bifurcation? | No: it stays a crossing and the daughters stay unowned (option a). Absorbing unrooted foreign neurites would move real data the wrong way. |
| N1-Q2 | An unrooted line passing exactly through a neurite's tip is a `T`, the same image as a T bifurcation. | Unchanged: like every 3-arm junction it is not a crossing. It is joined to the neuron as a branch, as on `main`. |

## New-case experiments

- A new topology class today would need a reserved value and a hand-written paint step. After: one `NeuriteTopologyClass` subclass with `plane_value` and `pixels`.
- A new consumer of crossing ownership (for example another per-owner measure) reads `shared_trace_owners()` or `crossing_routes`; nothing restates the crossing.

## Done when

The guards pass. The crossing family, intensity and bifurcation tests pass, and so do the existing crossing acceptance tests. The structural ratchet and NRA R1 show no regressions. The 30-workflow CellProfiler parity check is 30/30.
