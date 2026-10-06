"""Saved-record and real Pandoc/paired-build checks, without benchmark execution."""
from dataclasses import replace
import json
from pathlib import Path
import shutil
import subprocess
import zipfile

import pytest

from benchmark.reports.cppipe_figures import MeasuredBatchSummarySource
from paper_build.artifacts import InputObservations
from paper_build.cli import main
from paper_build.declarations import DocumentDefinition, DocumentRole, PaperDefinition, RetainedInputs
from paper_build.process import BuildLog
from build_paper import BENCHMARK_INCLUDE, ROOT, SlasDocumentBuilder, SlasRetainedFigures

RECORD = ROOT.parent / "benchmark/results/matched_final_20261006"


def sources(directory=RECORD / "data/singlewell"):
    return (MeasuredBatchSummarySource("one", directory / "execution_summary.csv"),
            MeasuredBatchSummarySource("one", directory / "total_summary.csv"))


def test_saved_record_projection_and_explicit_pending_freeze():
    execution, total = sources()
    pending = execution.publication_values(total, record_name=RECORD.name, frozen=False)
    frozen = execution.publication_values(total, record_name=RECORD.name, frozen=True)
    assert pending["status"] == "pending-final-freeze"
    for key in ("execution_min", "execution_median", "total_min", "total_median"):
        assert pending[key] == "PENDING"
    assert tuple(frozen[key] for key in ("execution_min", "execution_median", "total_min", "total_median")) == (
        "2.955", "4.401", "1.327", "3.370")
    assert frozen["case_count"] == "30"
    assert frozen["source_revision"] == "e905e77057e588f48df141634b4eb5b4a765095a"
    assert frozen["record_name"] == RECORD.name


@pytest.mark.parametrize("mutation", ("source", "cohort", "qualification", "numeric", "overflow"))
def test_mismatched_or_unqualified_inputs_do_not_become_claims(tmp_path, mutation):
    for filename in ("execution_summary.csv", "total_summary.csv", "summary_custody.json"):
        shutil.copy2(RECORD / "data/singlewell" / filename, tmp_path / filename)
    execution, total = sources(tmp_path)
    if mutation == "source":
        other = tmp_path / "other"
        other.mkdir()
        shutil.copy2(total.path, other / total.path.name)
        custody = total.qualified_custody()
        custody["source_head"] = "different"
        (other / "summary_custody.json").write_text(json.dumps(custody))
        total = replace(total, path=other / total.path.name)
    elif mutation == "qualification":
        custody = execution.qualified_custody()
        custody["status"] = "FAILED"
        execution.custody_path.write_text(json.dumps(custody))
    elif mutation == "cohort":
        lines = total.path.read_text().splitlines()
        total.path.write_text("\n".join(lines[:-1]) + "\n")
    elif mutation == "numeric":
        # A malformed explicit ratio cannot silently supply a claim.
        total.path.write_text(total.path.read_text().replace("2.7214147903204626", "nan", 1)
                             .replace("4.343241560738534", "nan", 1))
    else:
        # The generic row projection can overflow the fallback duration ratio;
        # publication must reject it rather than filter one case from statistics.
        total.path.write_text(total.path.read_text().replace("2.7214147903204626", "", 1)
                             .replace("4.343241560738534", "1e308", 1)
                             .replace("1.5959498626179993", "1e-308", 1))
    with pytest.raises(ValueError):
        execution.publication_values(total, record_name=RECORD.name, frozen=True)


def fixture_document(tmp_path, content):
    include = tmp_path / BENCHMARK_INCLUDE
    include.parent.mkdir(parents=True)
    shutil.copy2(ROOT / BENCHMARK_INCLUDE, include)
    source = tmp_path / "manuscript.md"
    source.write_text(content)
    definition = DocumentDefinition(DocumentRole.MANUSCRIPT, (Path(source.name),), citeproc=False)
    observations = InputObservations()
    return SlasDocumentBuilder().dependencies(definition, tmp_path, BuildLog(tmp_path / "parse.log"),
                                              observations, RetainedInputs()), source, observations


def test_pandoc_replaces_all_explicit_slots_not_unmarked_text(tmp_path):
    content = "\n\n".join(f"## {section}\n\nValue [old]{'{.benchmark-claim key=execution_min}'}; ordinary 2.86."
                             for section in ("Abstract", "Methods", "Results", "Figure 2 caption"))
    inputs, source, observations = fixture_document(tmp_path, content)
    converted = inputs.conversion_input({})
    assert converted.count('"c": "PENDING"') == 4
    assert '"c": "old"' not in converted
    assert '"c": "2.86."' in converted
    assert source.read_text() == content
    assert (tmp_path / BENCHMARK_INCLUDE).resolve() in inputs.support
    observations.verify()


def test_unknown_claim_does_not_keep_a_stale_number(tmp_path):
    with pytest.raises(KeyError):
        fixture_document(tmp_path, "[2.86]{.benchmark-claim key=made_up}")


def test_active_include_and_original_sources_match_existing_receipt(tmp_path):
    observations = InputObservations()
    publication = (ROOT / BENCHMARK_INCLUDE).parent
    figures = (publication / "measured_benchmark_publication.png",)
    checks = SlasRetainedFigures().resolve(ROOT, (*figures, (ROOT / BENCHMARK_INCLUDE).resolve()), observations)
    assert "retained outputs match" in checks[0]
    observations.verify()


def test_actual_paired_cli_candidate_renders_same_pending_claims(tmp_path):
    # A small declared reading packet exercises the original conversion/build
    # owner. It is not the parent's final manuscript or a scientific run.
    content = "# Benchmark claim receiving\n\n" + "\n\n".join(
        f"## {section}\n\nExecution minimum [old]{'{.benchmark-claim key=execution_min}'}; "
        f"total median [old]{'{.benchmark-claim key=total_median}'}; "
        f"record [old]{'{.benchmark-claim key=record_name}'}."
        for section in ("Abstract", "Methods", "Results", "Figure 2 caption"))
    publication = (ROOT / BENCHMARK_INCLUDE).parent
    for scope in ("execution", "total"):
        filename = f"measured_{scope}_speedup_cumulative_distribution_log.png"
        shutil.copy2(publication / scope / filename, tmp_path / filename)
        content += f"\n\n![{scope.title()} saved checkpoint.]({filename}){{width=5.5in}}\n"
    fixture_document(tmp_path, content)
    (tmp_path / "supplement.md").write_text("# Supplement\n\nSame minimum [old]{.benchmark-claim key=execution_min}.")
    declaration = Path(__file__).resolve()
    paper = PaperDefinition("slas-claim-receiving", tmp_path,
                            (DocumentDefinition(DocumentRole.MANUSCRIPT, (Path("manuscript.md"),), citeproc=False),
                             DocumentDefinition(DocumentRole.SUPPLEMENT, (Path("supplement.md"),), citeproc=False)),
                            declaration, RetainedInputs())
    assert main(paper, ["build", "--candidate"], builder=SlasDocumentBuilder()) == 0
    runs = tuple((tmp_path / "build").glob("run-*/build.json"))
    assert len(runs) == 1
    packet = runs[0].parent
    for stem in ("manuscript", "supplement"):
        with zipfile.ZipFile(packet / (stem + ".docx")) as archive:
            assert "PENDING" in archive.read("word/document.xml").decode()
        text = subprocess.check_output(("pdftotext", str(packet / (stem + ".pdf")), "-"), text=True)
        assert "PENDING" in text and "old" not in text
    assert not (tmp_path / "current").exists()
