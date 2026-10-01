Owned administrative supervisor failure
=======================================

Command handle23239, config-r1-context-restored. The supervisor raised
FileNotFoundError while measuring scratch during the R1 child's temporary
directory cleanup. Original failing statement:

.. code-block:: python

   scratch_bytes = sum(p.stat().st_size for p in scratch.rglob("*") if p.is_file())

Observed exception path:
/home/ts/.cache/agent-scratch/mcp-contract-fixtures-340-20261001/r1-full/
r1-zswn5p1o/0c0563e6538af313345391f2dc314270a86933a0/benchmark/results/
perf_lazy_cp_registry_20260929

Traceback descends run_bounded.py:30 -> pathlib.Path.rglob ->
_RecursiveWildcardSelector._select_from -> os.scandir, which raises
FileNotFoundError. No config-r1-context-restored.command.json was created;
do not infer a final peak RSS, returned child exit code or passed ratchet.

The actual retained child log independently ends with
nominal_refactor_advisor.deadline.ScanDeadlineExceeded:
scan deadline exceeded during parse_python_module:55.000s/55.000s.
No baseline/head comparison exists. Subsequent process census confirms the
R1 child and supervisor are absent; there is no live scan to restart or adopt.

Fix is scoped only to the parent's disposable administrative supervisor:
os.walk tolerates disappearing directories; per-file stat tolerates
FileNotFoundError. Product code, NRA, original R1 roots/detectors/inputs,
timeouts and scientific harnesses are unchanged. No additional R1 run is
claimed from that administrative fix.
