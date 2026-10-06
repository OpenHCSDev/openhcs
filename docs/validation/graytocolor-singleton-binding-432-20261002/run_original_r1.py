"""Run the unchanged R1 owner against exact Git trees, without source checkouts.

Only small, disposable local Git metadata views are created. The original
policy owns source materialization, all three roots/eight recorded dependencies,
detector selection, source/dependency identity, deadlines and comparison.
"""

import json
from pathlib import Path
import subprocess
import sys


def git_output(repo, *args):
    return subprocess.check_output(("git", "-C", str(repo), *args), text=True).strip()


def main():
    source_root = Path(__file__).resolve().parents[3]
    scratch = Path(sys.argv[1])
    base, head = sys.argv[2:4]
    scratch.mkdir(parents=True, exist_ok=True)
    view = scratch / "git-view"
    common = Path(git_output(source_root, "rev-parse", "--git-common-dir")).resolve()
    store_overrides = dict(argument.split("=", 1) for argument in sys.argv[4:])
    dependencies = {}
    for revision in (base, head):
        for entry in git_output(source_root, "ls-tree", "-r", revision).splitlines():
            metadata, path = entry.split("\t", 1)
            mode, _kind, oid = metadata.split()
            if mode == "160000":
                dependencies.setdefault(path, set()).add(oid)
    stores = {path: Path(store_overrides.get(path, common / "modules" / path))
              for path in dependencies}
    for path, object_ids in sorted(dependencies.items()):
        for oid in sorted(object_ids):
            git_output(stores[path], "cat-file", "-e", f"{oid}^{{commit}}")
    print("Read-only exact dependency stores:",
          {path: str(store) for path, store in sorted(stores.items())}, flush=True)
    subprocess.run(("git", "clone", "--shared", "--no-checkout", "--no-tags",
                    str(source_root), str(view)), check=True)
    for path, object_ids in sorted(dependencies.items()):
        store = stores[path]
        # Read exact original object stores. No fetch, checkout or source writes.
        subprocess.run(("git", "clone", "--shared", "--no-checkout", "--no-tags",
                        str(store), str(view / path)), check=True)
        for oid in sorted(object_ids):
            git_output(view / path, "cat-file", "-e", f"{oid}^{{commit}}")
    print("Exact original R1 dependency context:",
          {path: sorted(ids) for path, ids in sorted(dependencies.items())}, flush=True)
    sys.path.insert(0, str(source_root))
    from scripts.check_refactor_r1 import compare
    from nominal_refactor_advisor.json_reports import json_report_object
    result = compare(view, base, head, scratch / "scan", budget_seconds=55)
    print(json.dumps(json_report_object(result), indent=2), flush=True)
    return int(bool(result.increased))


if __name__ == "__main__":
    raise SystemExit(main())
