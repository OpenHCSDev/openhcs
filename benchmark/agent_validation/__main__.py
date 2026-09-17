"""Command-line entry point for the autonomous validation corpus."""

from __future__ import annotations

import argparse
from pathlib import Path

from benchmark.agent_validation.corpus import AgentValidationCorpus
from benchmark.agent_validation.provenance import verify_upstream_checkout


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Build and audit blind autonomous image-analysis tasks."
    )
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("list", help="List declaration-owned task ids.")
    build = subparsers.add_parser(
        "build", help="Write an answer-free authoring bundle."
    )
    build.add_argument("output_root", type=Path)
    diagnostics = subparsers.add_parser(
        "build-diagnostics", help="Write opaque failure-diagnosis challenges."
    )
    diagnostics.add_argument("output_root", type=Path)
    verify = subparsers.add_parser(
        "verify-upstream",
        help="Verify a pinned human-eval-bia checkout without executing it.",
    )
    verify.add_argument("checkout", type=Path)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    if args.command == "list":
        for declaration in AgentValidationCorpus.task_declarations():
            print(declaration.task_id)
        return 0
    if args.command == "build":
        specs = AgentValidationCorpus.build_authoring_bundle(args.output_root)
        print(f"Wrote {len(specs)} blind tasks to {args.output_root}")
        return 0
    if args.command == "build-diagnostics":
        probe_ids = AgentValidationCorpus.build_diagnostic_bundle(args.output_root)
        print(f"Wrote {len(probe_ids)} diagnostic probes to {args.output_root}")
        return 0
    results = verify_upstream_checkout(args.checkout)
    for result in results:
        print(
            f"{result.task_id}: notebook={result.notebook_matches} "
            f"check_source={result.check_source_matches}"
        )
    return 0 if all(result.passed for result in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
