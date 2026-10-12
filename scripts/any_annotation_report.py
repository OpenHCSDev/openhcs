"""Where `typing.Any` is written as a declared type, and who owns each use.

This is a report over the packaged ratchet measure, not another detector:
`agent_comms.debt_ratchet.AnyAnnotation` owns what counts as a use (parameters,
returns, annotated assignments and aliases; nested and quoted). This script
adds the one OpenHCS fact the measure cannot know: whether the declaration is
read by a form, the code document or MCP.

Two steps, because the two facts live in different environments:

    # 1. live owners, in the OpenHCS environment (imports openhcs, runs discovery)
    python -m scripts.any_annotation_report owners --out owners.json

    # 2. the report, with the pinned ratchet (same pin as refactor-guardrails.yml)
    uv run --no-project --python 3.14 --with git+https://github.com/OpenHCSDev/agent-comms@<pin> \\
        python -m scripts.any_annotation_report report --owners owners.json \\
        openhcs external/ObjectState/src ...
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from dataclasses import asdict, dataclass, fields, is_dataclass
from pathlib import Path


@dataclass(frozen=True)
class LiveOwners:
    """Declarations a user reaches, as `module:qualname`, read from a live import."""

    config_dataclasses: tuple[str, ...] = ()
    catalogued_functions: tuple[str, ...] = ()

    @classmethod
    def discover(cls) -> LiveOwners:
        import inspect
        import typing

        import openhcs.core.config  # noqa: F401  (declares the config family)
        from objectstate.lazy_factory import (
            LazyDataclassFactory,
            is_global_config_type,
        )
        from openhcs.core.config import GlobalPipelineConfig
        from openhcs.processing.backends.lib_registry.openhcs_registry import OpenHCSRegistry

        def dataclasses_in(annotation: object):
            if is_dataclass(annotation):
                yield annotation
            for member in typing.get_args(annotation):
                yield from dataclasses_in(member)

        assert is_global_config_type(GlobalPipelineConfig)
        pending = [GlobalPipelineConfig]
        for lazy_type, base_type in LazyDataclassFactory.registered_type_pairs():
            pending += [lazy_type, base_type]
        functions = tuple(
            inspect.unwrap(metadata.func)
            for metadata in OpenHCSRegistry().discover_functions().values()
        )
        reached: set[type] = set()
        while pending:
            config_type = pending.pop()
            if config_type in reached:
                continue
            reached.add(config_type)
            hints = typing.get_type_hints(config_type)
            for declared in fields(config_type):
                pending.extend(dataclasses_in(hints[declared.name]))
        return cls(
            config_dataclasses=tuple(sorted(
                f"{config_type.__module__}:{config_type.__qualname__}" for config_type in reached
            )),
            catalogued_functions=tuple(sorted(
                f"{function.__module__}:{function.__qualname__}" for function in functions
            )),
        )


@dataclass(frozen=True)
class OwnedUse:
    package: str
    path: str
    line: int
    site: str
    owner: str
    owner_kind: str


class OwnerKinds:
    """Name the owner of one use from the live declarations."""

    def __init__(self, live: LiveOwners) -> None:
        self.config = frozenset(live.config_dataclasses)
        self.catalogued = frozenset(live.catalogued_functions)

    def kind(self, module: str, use) -> str:
        declared = f"{module}:{use.owner}"
        if declared in self.config:
            return "config dataclass"
        if declared in self.catalogued:
            return "catalogued function"
        if use.site == "dataclass field":
            return "DTO"
        return "internal"


def module_name(root: Path, path: Path) -> str:
    package_parent = root.parent if (root / "__init__.py").exists() else root
    return ".".join(path.relative_to(package_parent).with_suffix("").parts).removesuffix(".__init__")


def uses_under(root: Path, kinds: OwnerKinds) -> list[OwnedUse]:
    from agent_comms.debt_ratchet import AnyAnnotation

    found = []
    for path in sorted(root.rglob("*.py")):
        module = module_name(root, path)
        for use in AnyAnnotation.uses(path.read_bytes(), str(path)):
            found.append(OwnedUse(
                package=root.as_posix(), path=path.as_posix(), line=use.line,
                site=use.site, owner=use.owner, owner_kind=kinds.kind(module, use),
            ))
    return found


def table(title: str, counts: Counter, limit: int | None = None) -> str:
    rows = [f"| {title} | uses |", "|---|---:|"]
    rows += [f"| {name} | {count} |" for name, count in counts.most_common(limit)]
    return "\n".join(rows)


def report(roots: list[Path], kinds: OwnerKinds, top: int) -> tuple[str, list[OwnedUse]]:
    uses = [use for root in roots for use in uses_under(root, kinds)]
    sections = [
        table("package", Counter(use.package for use in uses)),
        table("declared as", Counter(use.site for use in uses)),
        table("owner", Counter(use.owner_kind for use in uses)),
        table(f"top {top} files", Counter(use.path for use in uses), top),
    ]
    user_facing = [use for use in uses if use.owner_kind in ("config dataclass", "catalogued function")]
    listed = [f"- `{use.path}:{use.line}` {use.owner_kind} `{use.owner}` ({use.site})" for use in user_facing]
    sections.append("\n".join([f"User-facing uses: {len(user_facing)}", *listed]))
    return "\n\n".join(sections), uses


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    owners = commands.add_parser("owners", help="write the live user-facing declarations")
    owners.add_argument("--out", type=Path, required=True)
    reporting = commands.add_parser("report", help="print the tables for the given source trees")
    reporting.add_argument("roots", type=Path, nargs="+")
    reporting.add_argument("--owners", type=Path, required=True)
    reporting.add_argument("--top", type=int, default=25)
    reporting.add_argument("--json", type=Path, help="also write every use as JSON")
    args = parser.parse_args()

    if args.command == "owners":
        args.out.write_text(json.dumps(asdict(LiveOwners.discover()), indent=1))
        return 0
    live = LiveOwners(**{
        name: tuple(values) for name, values in json.loads(args.owners.read_text()).items()
    })
    text, uses = report(args.roots, OwnerKinds(live), args.top)
    print(text)
    if args.json:
        args.json.write_text(json.dumps([asdict(use) for use in uses], indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
