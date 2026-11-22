"""Command-line entry point for the autonomous validation corpus."""

from __future__ import annotations

import argparse
import json
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
    one = subparsers.add_parser(
        "build-task",
        help="Write one blind task that `check` can read the result of.",
    )
    one.add_argument("task_root", type=Path)
    one.add_argument("--pick", type=int, required=True,
                     help="which of those tasks, counted around in declaration order")
    check = subparsers.add_parser(
        "check",
        help="Check the plate an OpenHCS run wrote beside one task's inputs against "
        "the task's held-out cases.",
    )
    check.add_argument("task_root", type=Path)
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
    if args.command == "build-task":
        print(AgentValidationCorpus.build_task(args.task_root, args.pick).task_id)
        return 0
    if args.command == "check":
        assertions = AgentValidationCorpus.check_output_plate(args.task_root)
        for assertion in assertions:
            print(json.dumps({"name": assertion.name, "passed": assertion.passed,
                              "detail": assertion.detail}, sort_keys=True))
        return 0 if assertions and all(assertion.passed for assertion in assertions) else 1
    results = verify_upstream_checkout(args.checkout)
    for result in results:
        print(
            f"{result.task_id}: notebook={result.notebook_matches} "
            f"check_source={result.check_source_matches}"
        )
    return 0 if all(result.passed for result in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
