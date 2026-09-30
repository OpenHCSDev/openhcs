from pathlib import Path
from nominal_refactor_advisor.codemod import CodemodPlanDocument,CodemodSourceSnapshot,PatchTargetOperation,RefactorRecipe,SourceRewriteTarget,SourceTextReplacement
root=Path('/home/ts/code/projects/openhcs-compile-perf');path=root/'benchmark/matched_cellprofiler_batch.py';source=path.read_text()
a=source.index('    process = subprocess.run(',source.index('def _invoke_native_worker('));b=source.index('\n\ndef _worker_axis_evidence(',a)
new='''    report_path = evidence_prefix.with_name(evidence_prefix.name + "_report.json").resolve()
    request = json.loads(request_path.read_text())
    request["report_path"] = str(report_path)
    request_path.write_text(json.dumps(request, indent=2) + "\\n")
    with (
        evidence_prefix.with_name(evidence_prefix.name + "_stdout.log").open("w") as stdout,
        evidence_prefix.with_name(evidence_prefix.name + "_stderr.log").open("w") as stderr,
    ):
        process = subprocess.run(
            (str(native_python), str(worker_script), str(request_path)),
            cwd=project_root,
            env=native_environment,
            stdout=stdout,
            stderr=stderr,
            text=True,
            timeout=900 * (repetitions + 1),
            check=False,
        )
    process.check_returncode()
    return json.loads(report_path.read_text())
'''
worker=root/'benchmark/native_cellprofiler_batch_worker.py';worker_source=worker.read_text()
operation=PatchTargetOperation(target=SourceRewriteTarget(file_path=str(path)),replacements=(SourceTextReplacement(old_source=source[a:b],new_source=new),),rationale='The one shared native-worker bridge projects existing report_path and durable log files before launching, consumes the worker-owned report and retires in-memory stdout JSON transport. Both current drivers derive from this authority.')
worker_operation=PatchTargetOperation(target=SourceRewriteTarget(file_path=str(worker)),replacements=(SourceTextReplacement(old_source='        print(json.dumps(report))',new_source='        else:\n            print(json.dumps(report))'),),rationale='Keep stdout JSON only for the genuinely standalone no-report-file boundary; file-report workers do not depend on a live stdout reader to emit completion.')
sources={str(path):source,str(worker):worker_source};plan=CodemodPlanDocument(recipes=(RefactorRecipe(recipe_id='durable-native-batch-evidence',operations=(operation,worker_operation),reason='Issue #246 observed controller-pipe evidence loss; reuse existing worker report authority and one shared bridge.'),));simulation=plan.simulate(CodemodSourceSnapshot.from_source_mapping(sources));assert simulation.is_clean,simulation.simulation_payload()
(root.parent/'openhcs-benchmark-runs/perf-native-batch-durability-nra-projected-20260929.diff').write_text(simulation.unified_diff(sources));print(simulation.apply())
