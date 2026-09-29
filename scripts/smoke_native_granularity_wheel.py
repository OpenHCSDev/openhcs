"""Exercise the installed stable-ABI granularity extension without core dependencies."""

from array import array
from importlib import metadata, util

distribution = metadata.distribution("openhcs")
extension_path = next(
    distribution.locate_file(entry)
    for entry in distribution.files or ()
    if entry.name.startswith("_granularity_reconstruct")
    and entry.name.endswith((".so", ".pyd"))
)
spec = util.spec_from_file_location("_granularity_reconstruct", extension_path)
assert spec is not None and spec.loader is not None
module = util.module_from_spec(spec)
spec.loader.exec_module(module)


def image(values):
    return memoryview(array("f", values)).cast("B").cast("f", shape=(3, 3))


seed = image([0, 0, 0, 0, 1, 0, 0, 0, 0])
mask = image([1] * 9)
output = image([0] * 9)
module.reconstruct_f32(
    seed,
    mask,
    output,
    memoryview(array("I", [0] * 9)),
    memoryview(array("I", [0] * 9)),
    memoryview(array("B", [0] * 9)),
)
assert all(output[row, col] == 1 for row in range(3) for col in range(3))
