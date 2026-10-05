"""Source-only diagnostic: deny catalogue preparation and native execution."""

import importlib.util
import cProfile
import pstats
import sys
import time
import traceback
from pathlib import Path

# Reuse only the parent's existing ABI substrate, without source/install writes.
import openhcs

# The executable may resolve to a shared Python; the supplied readonly root is
# explicit so it never guesses an installed incarnation from that executable.
installed_package = Path(sys.argv[1])
for module_name, relative in (
    ("openhcs.core._tabular_native", "core/_tabular_native.abi3.so"),
    (
        "openhcs.processing.backends.cellprofiler._granularity_native",
        "processing/backends/cellprofiler/_granularity_native.abi3.so",
    ),
):
    spec = importlib.util.spec_from_file_location(module_name, installed_package / relative)
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)

started = time.monotonic()
from openhcs.processing.backends.lib_registry.registry_service import RegistryService


def denied_preparation(*args, **kwargs):
    traceback.print_stack()
    raise AssertionError("source retrieval attempted unrelated catalog preparation")


RegistryService.prepare_persistent_catalog = denied_preparation
RegistryService.prepare_in_current_process = denied_preparation

print("registry imported", time.monotonic() - started, flush=True)
from openhcs.agent.dto.knowledge import KnowledgeBaseDocumentRequest
from openhcs.agent.services.knowledge_base_service import KnowledgeBaseService

print("knowledge imported", time.monotonic() - started, flush=True)
profile = cProfile.Profile()
profile.enable()
document = KnowledgeBaseService().get_document(
    KnowledgeBaseDocumentRequest.from_fields(
        document_id="openhcs_official30_benchmark_recipes",
        section_id="cp-tutorial-pixel-based-classification-openhcs-python",
        max_chars=50000,
    )
)
profile.disable()
print("completed", time.monotonic() - started, flush=True)
print("errors", document.errors, flush=True)
print("content_chars", len(document.content), flush=True)
pstats.Stats(profile).sort_stats("cumulative").print_stats(35)
assert not document.errors
