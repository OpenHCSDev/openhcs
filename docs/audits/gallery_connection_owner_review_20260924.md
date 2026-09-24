# Gallery connection declaration owner review (2026-09-24)

The shared `ExecutionConnectionSpec` declaration moved unchanged from
`openhcs/agent/dto/execution.py` into
`openhcs/agent/dto/execution_connection.py`. The former module re-exports the
same class for existing clients. `scripts/gallery_catalog.py` now imports the
lightweight owner at runtime, so its `GallerySourceCaptureRequest` annotation
is resolvable by `typing.get_type_hints` and `dataclass_from_mapping` without
loading the heavy execution DTO graph or pandas during website validation.

This is an import/ownership change, not a gallery scenario, capture target,
connection field, protocol, job-status, or progress-projection change. The
existing audited user and development pages that cite `scripts/gallery_catalog.py`
retain their scenario and publication claims. The two pages citing
`openhcs/agent/dto/execution.py` for job/progress DTOs retain those claims;
the moved connection declaration was not the authority for those claims.

Validation: the focused gallery request round-trip test passed; a fresh import
of the catalog left `pandas` unloaded and `get_type_hints` resolved the
connection type. The gallery and website unit group passed (63 tests), and
documentation validation passed (155 audited sources). The agent-service group
passed 106 tests; its one function-catalog preparation test failed with an
`EDQUOT` disk-quota error in a subprocess, not a connection-declaration
assertion. Full CI remains the publication gate.
