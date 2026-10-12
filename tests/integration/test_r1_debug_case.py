"""TEMPORARY (surface R1z): run named Official30 cases as the parity test does and keep the tables."""

import os
from pathlib import Path

import pytest

from benchmark.cellprofiler_comparison import load_comparison_cases, run_comparison_suite
from openhcs.core.config import GlobalPipelineConfig, LazyNapariStreamingConfig, PartitionFilterConfig
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG
from zmqruntime import DataControlPortPairAuthority

REPO = Path(__file__).resolve().parents[2]


@pytest.mark.integration
def test_r1_debug_cases():
    names = set(os.environ["R1_CASES"].split())
    out = Path(os.environ["R1_OUT"])
    cases = [
        c
        for c in load_comparison_cases(REPO / "benchmark/manifests/official30_portable_axis1.json")
        if c.name in names
    ]
    assert len(cases) == len(names)
    port = DataControlPortPairAuthority.acquire(
        OPENHCS_ZMQ_CONFIG, transport_mode=OPENHCS_ZMQ_CONFIG.transport_mode, excluded=set()
    ).data_port
    observations = run_comparison_suite(
        cases,
        output_root=out,
        suite_id="r1-debug",
        native_reference_root=Path(os.environ["OPENHCS_CP_NATIVE_REFERENCE_ROOT"]),
        require_native_reference=True,
        openhcs_global_config=GlobalPipelineConfig(
            partition_filter_config=PartitionFilterConfig(partition_filter=1),
            napari_streaming_config=LazyNapariStreamingConfig(enabled=False, persistent=False),
        ),
        discard_openhcs_outputs=False,
        continue_on_error=True,
        openhcs_execution_port=port,
    )
    for observation in observations:
        print(f"== {observation.case_name}: equivalent={observation.equivalent}")
        for side in (observation.native_cellprofiler, observation.openhcs):
            if side.error_message:
                print(side.error_message[-6000:])
            print("output", side.output_path)
    assert all(observation.equivalent for observation in observations)
