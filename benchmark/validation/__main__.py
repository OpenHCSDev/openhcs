"""Command-line interface for independent-reference validation corpora."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, is_dataclass
from enum import Enum
from pathlib import Path
from typing import Any

from benchmark.datasets.registry import get_dataset_spec
from benchmark.validation.corpus import ValidationCorpusPreparer, freeze_pipeline
from benchmark.validation.scoring import score_validation_corpus


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Prepare and score declaration-owned independent validation data."
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    describe = subparsers.add_parser(
        "describe", help="Print pinned dataset provenance."
    )
    describe.add_argument("dataset_id")

    prepare = subparsers.add_parser(
        "prepare", help="Build separated authoring/scoring roots."
    )
    prepare.add_argument("dataset_id")
    prepare.add_argument("--output-root", type=Path, required=True)
    prepare.add_argument("--cache-root", type=Path, required=True)

    freeze = subparsers.add_parser("freeze", help="Hash-freeze a completed pipeline.")
    freeze.add_argument("dataset_id")
    freeze.add_argument("pipeline", type=Path)
    freeze.add_argument("--corpus-root", type=Path, required=True)

    score = subparsers.add_parser("score", help="Score outputs after pipeline freeze.")
    score.add_argument("dataset_id")
    score.add_argument("result", type=Path)
    score.add_argument("--corpus-root", type=Path, required=True)
    score.add_argument("--report", type=Path, required=True)
    return parser


def main(argv: list[str] | None = None) -> int:
    """Execute one validation-corpus command."""

    args = _parser().parse_args(argv)
    if args.command == "describe":
        validation = get_dataset_spec(args.dataset_id).independent_validation
        if validation is None:
            raise ValueError(
                f"Dataset {args.dataset_id!r} has no independent-validation declaration."
            )
        print(json.dumps(_jsonable(validation), indent=2, sort_keys=True))
        return 0
    if args.command == "prepare":
        prepared = ValidationCorpusPreparer().prepare(
            args.dataset_id,
            output_root=args.output_root,
            cache_root=args.cache_root,
        )
        print(json.dumps(_jsonable(prepared), indent=2, sort_keys=True))
        return 0
    if args.command == "freeze":
        receipt = freeze_pipeline(
            args.dataset_id,
            args.pipeline,
            corpus_root=args.corpus_root,
        )
        print(json.dumps(_jsonable(receipt), indent=2, sort_keys=True))
        return 0
    report = score_validation_corpus(
        args.dataset_id,
        corpus_root=args.corpus_root,
        result_path=args.result,
        report_path=args.report,
    )
    print(json.dumps(_jsonable(report), indent=2, sort_keys=True))
    return 0


def _jsonable(value: Any) -> Any:
    if is_dataclass(value) and not isinstance(value, type):
        return _jsonable(asdict(value))
    if isinstance(value, Enum):
        return value.value
    if isinstance(value, Path):
        return str(value)
    if isinstance(value, dict):
        return {str(key): _jsonable(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [_jsonable(item) for item in value]
    return value


if __name__ == "__main__":
    raise SystemExit(main())
