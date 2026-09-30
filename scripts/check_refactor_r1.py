"""Changed-file R1 ratchet using NRA's original declarations and certificates.

This is a scoped policy consumer, not another detector or schema inventory.
Git owns revision/submodule membership; NRA owns parsing, schema resolution,
constructor descent, attribute contracts and missing-descent certificates.
"""

from __future__ import annotations

import argparse
import io
import json
import subprocess
import sys
import tarfile
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from tempfile import TemporaryDirectory

from nominal_refactor_advisor.analysis import (
    AnalysisPathScope,
    analyze_compact_roots_with_cache,
)
from nominal_refactor_advisor.deadline import ScanDeadline, enforce_scan_deadline
from nominal_refactor_advisor.detectors import (
    RedundantTypeCheckDetector,
    UnmodeledRecordShapeDetector,
)
from nominal_refactor_advisor.json_reports import (
    SemanticRecord,
    json_report_object,
    json_report_property,
)
from nominal_refactor_advisor.semantic_descent import (
    PresentationProjectionKind,
    ResolvedDescentCertificate,
    SemanticAuthorityKind,
)


def git(repo: Path, *arguments: str) -> bytes:
    return subprocess.run(
        ("git", "-C", str(repo), *arguments), check=True, stdout=subprocess.PIPE
    ).stdout


@dataclass(frozen=True)
class SourceRevision:
    repo: Path
    revision: str

    def materialize(self, destination: Path, roots: tuple[str, ...] = ()) -> None:
        """Read committed Python only, recursively at recorded gitlink objects."""
        if (
            Path(git(self.repo, "rev-parse", "--show-toplevel").decode().strip())
            != self.repo.resolve()
        ):
            raise RuntimeError(
                f"Recorded source repository is not initialized: {self.repo}"
            )
        if roots:
            roots = tuple(
                root
                for root in roots
                if git(self.repo, "ls-tree", self.revision, "--", root)
            )
            if not roots:
                return
        with tarfile.open(
            fileobj=io.BytesIO(git(self.repo, "archive", self.revision, *roots))
        ) as archive:
            for member in archive:
                if not member.name.endswith(".py"):
                    continue
                if not member.isfile():
                    raise ValueError(f"Non-regular Python source: {member.name}")
                archive.extract(member, destination, filter="data")
        for entry in git(self.repo, "ls-tree", "-r", "-z", self.revision).split(b"\0"):
            if not entry:
                continue
            metadata, path_bytes = entry.split(b"\t", 1)
            mode, _kind, object_id = metadata.decode().split()
            if mode != "160000":
                continue
            path = path_bytes.decode()
            # All recorded dependency sources are context, not a companion roster.
            SourceRevision(self.repo / path, object_id).materialize(destination / path)


@dataclass(frozen=True, order=True)
class R1Count(SemanticRecord):
    check: str
    file: str
    count: int


def scan_counts(
    snapshot: Path,
    roots: tuple[str, ...],
    changed: tuple[str, ...],
    *,
    cache_root: Path,
) -> tuple[R1Count, ...]:
    context = tuple(snapshot / root for root in roots if (snapshot / root).exists())
    dependency_context = snapshot / "external"
    if dependency_context.exists():
        context += (dependency_context,)
    reports = tuple(snapshot / path for path in changed if (snapshot / path).is_file())
    if not reports:
        return ()
    result = analyze_compact_roots_with_cache(
        context,
        detector_types=(RedundantTypeCheckDetector, UnmodeledRecordShapeDetector),
        report_scope=AnalysisPathScope(context, reports),
        parse_workers=1,
        cache_dir=cache_root / "parse",
        analysis_cache_dir=cache_root / "analysis",
        include_semantic_descent_graph=True,
    )
    print(
        f"R1 {snapshot.name}: NRA cache={result.cache_status.value}, "
        f"projections={result.projection_count}, "
        f"prepare={result.preparation_seconds:.3f}s, "
        f"analysis={result.analysis_seconds:.3f}s",
        file=sys.stderr,
    )
    graph = result.semantic_descent_graph
    if graph is None:
        raise RuntimeError("NRA omitted the required schema/descent context")
    counts: Counter[tuple[str, str]] = Counter()
    selected = set(changed)
    for finding in result.findings:
        # R1 evidence is source/check first; redundant checks also carry the
        # declaration as secondary evidence. Unmodeled shapes carry read sites.
        sites = finding.evidence
        if finding.detector_id == RedundantTypeCheckDetector().detector_id:
            sites = sites[:1]
        for site in sites:
            path = Path(site.file_path).relative_to(snapshot).as_posix()
            if path in selected:
                counts[finding.detector_id, path] += 1
    for certificate in graph.missing_descent_certificates:
        resolved = ResolvedDescentCertificate.from_graph(graph, certificate)
        if resolved.projection.kind is not PresentationProjectionKind.MAPPING_READ:
            continue
        if resolved.authority.kind is not SemanticAuthorityKind.DATACLASS_SCHEMA:
            continue
        path = (
            Path(resolved.projection.location.file_path)
            .relative_to(snapshot)
            .as_posix()
        )
        if path in selected:
            counts[resolved.projection.kind.value, path] += 1
    return tuple(
        R1Count(check, path, count) for (check, path), count in sorted(counts.items())
    )


@dataclass(frozen=True)
class R1Comparison(SemanticRecord):
    base: str
    head: str
    changed: tuple[str, ...]
    before: tuple[R1Count, ...]
    after: tuple[R1Count, ...]

    @json_report_property()
    def increased(self) -> tuple[R1Count, ...]:
        baseline = {(item.check, item.file): item.count for item in self.before}
        return tuple(
            R1Count(
                item.check,
                item.file,
                item.count - baseline.get((item.check, item.file), 0),
            )
            for item in self.after
            if item.count > baseline.get((item.check, item.file), 0)
        )


def compare(
    repo: Path,
    base: str,
    head: str,
    scratch_root: Path,
    *,
    budget_seconds: float = 160,
    roots: tuple[str, ...] = ("openhcs", "scripts", "benchmark"),
) -> R1Comparison:
    base, head = (
        git(repo, "rev-parse", "--verify", f"{ref}^{{commit}}").decode().strip()
        for ref in (base, head)
    )
    changed = tuple(
        path.decode()
        for path in git(
            repo, "diff", "--no-renames", "--name-only", "-z", base, head, "--", *roots
        ).split(b"\0")
        if path.endswith(b".py")
    )
    if not changed:
        return R1Comparison(base, head, (), (), ())
    scratch_root.mkdir(parents=True, exist_ok=True)
    with TemporaryDirectory(prefix="r1-", dir=scratch_root) as temporary:
        work = Path(temporary)
        results = []
        with enforce_scan_deadline(ScanDeadline.start(budget_seconds)):
            for revision in (base, head):
                snapshot = work / revision
                snapshot.mkdir()
                SourceRevision(repo, revision).materialize(snapshot, roots)
                results.append(
                    scan_counts(snapshot, roots, changed, cache_root=work / "nra")
                )
        return R1Comparison(base, head, changed, *results)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", required=True)
    parser.add_argument("--head", required=True)
    parser.add_argument("--scratch-root", required=True, type=Path)
    parser.add_argument("--budget-seconds", type=float, default=160)
    args = parser.parse_args()
    result = compare(
        Path.cwd(),
        args.base,
        args.head,
        args.scratch_root,
        budget_seconds=args.budget_seconds,
    )
    print(json.dumps(json_report_object(result), indent=2))
    return int(bool(result.increased))


if __name__ == "__main__":
    raise SystemExit(main())
