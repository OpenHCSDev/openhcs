"""New synthetic failed source; never a scientific source revision."""
import numpy as np
from openhcs.core.xdg_paths import get_data_file_path

scratch = np.ones((1024, 1024), dtype=np.uint8)


class SourceOnlyFault(RuntimeError):
    def source_value(self):
        return scratch[0, 0]


@numpy
def retention_failure_fixture(image):
    return image


with get_data_file_path("source-executions.txt").open("a") as output:
    output.write("failure source executed\n")
raise SourceOnlyFault("new synthetic failed-source evidence")
