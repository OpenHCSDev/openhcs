# Fiji in tests

Pytest pins PolyStore's Fiji bundle cache before collecting tests. Changing
`XDG_CACHE_HOME` inside a test does not move that bundle or download another copy.
The same cache selector is inherited by native child processes. Logs, preferences,
and other fixture state remain isolated.

Ordinary tests default to `POLYSTORE_IMAGEJ_ALLOW_DOWNLOAD=false`. An absent or
invalid bundle fails before network access or staging-directory creation. Fiji is
not required for tests that do not use it.

To provision Fiji intentionally, run the existing managed runtime prewarm before
pytest, or explicitly set `POLYSTORE_IMAGEJ_ALLOW_DOWNLOAD=true` for provisioning.
When a launcher isolates `XDG_CACHE_HOME` **before starting pytest**, point
`POLYSTORE_IMAGEJ_CACHE_ROOT` at the persistent bundle cache before launch. Explicit
selectors are validated and never silently replaced. CI caches the actual
PolyStore bundle directory and prewarms it outside pytest.
