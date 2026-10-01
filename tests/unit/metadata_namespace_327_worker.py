"""Native process recipient; import dependency before application on purpose."""

import pickle
import sys
from pathlib import Path

import numpy as np
import polystore.metadata_writer

import openhcs


def main():
    from polystore.base import ImageSamplingRequest

    assert (
        Path(openhcs.__file__).resolve().parents[1]
        == Path(__file__).resolve().parents[2]
    )
    assert (
        Path(polystore.metadata_writer.__file__).resolve()
        == Path(sys.argv[2]).resolve()
    )
    with Path(sys.argv[1]).open("rb") as stream:
        manager, root, config, expected = pickle.load(stream)
    workspace = manager.registry["virtual_workspace"]
    assert workspace.metadata_config == config
    assert workspace.metadata_config.__class__ is config.__class__
    assert workspace._registry is manager.registry
    np.testing.assert_array_equal(
        manager.load(root / "virtual.npy", backend="virtual_workspace"), expected
    )
    sample = manager.sample(
        root / "virtual.npy",
        backend="virtual_workspace",
        request=ImageSamplingRequest(origin_yx=(1, 1), shape_yx=(2, 3)),
    )
    np.testing.assert_array_equal(sample.data, expected[1:3, 1:4])
    assert sample.source_shape == expected.shape
    assert workspace._resolve_ref(root / "virtual.npy").source_axis_indices == (1,)
    print("native handoff: exact application namespace, pixels and provenance")


if __name__ == "__main__":
    main()
