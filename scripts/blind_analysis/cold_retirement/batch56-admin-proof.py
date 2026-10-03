"""Future parameter/receipt consumer of the immutable Batch56/39 performer.

No archive algorithm is copied here. Preparation binds the existing owner;
execution still delegates admission and all proof/retirement to that owner.
"""
import argparse
import ast
import json
from pathlib import Path


RECORDED = Path(
    "/home/ts/wt/openhcs-issue-batch-20260929/"
    "neurite-development-skill383-20261001/output/resource-owner-20261002"
)
CREATOR = Path(__file__).with_name("restore_creator.py")


def configure(arguments):
    owner = RECORDED / "batch39-cold-proof.py"
    tree = ast.parse(owner.read_text())
    driver = ast.parse((RECORDED / "batch56-admin-proof02.py").read_text())
    declaration = next(
        node.value for node in driver.body
        if isinstance(node, ast.Assign)
        and any(isinstance(target, ast.Name) and target.id == "admission" for target in node.targets)
    )
    # Reuse the original Batch56 admission declaration, not its old invocation.
    admission = eval(
        compile(ast.Expression(declaration), "<original Batch56 admission>", "eval"),
        {"ast": ast, "root": str(arguments.fund.parent)},
    )
    old_resource = str(arguments.fund.parent) + "/RUN/operations/resource-check.sh"
    old_fund = str(arguments.fund.parent) + "/FUND"
    route = {
        old_resource: str(arguments.operations / "resource-check.sh"),
        old_fund: str(arguments.fund),
        old_fund + "/program.json": str(arguments.fund / "program.json"),
        "ADMIN_RECEIVING": arguments.slot,
        "dalton56_proof02_": arguments.phase_prefix + "_",
    }
    for declaration_node in admission:
        for node in ast.walk(declaration_node):
            # The recorded declaration constructs these strings as BinOps.
            if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
                if isinstance(node.left, ast.Constant) and isinstance(node.right, ast.Constant):
                    value = node.left.value + node.right.value
                    if value in route:
                        node.left.value, node.right.value = route[value], ""
            if isinstance(node, ast.Constant) and isinstance(node.value, str):
                node.value = route.get(node.value, node.value)

    bindings = {
        "SOURCE": arguments.source,
        "ARCHIVE": arguments.archive,
        "RESTORE": arguments.restore,
        "RECEIPTS": arguments.receipts,
        "FUNDING": arguments.funding_receipt,
        "proof": RECORDED / "batch36-xz02-proof.py",
    }
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef) and node.name == "record":
            # Original Batch56 compact stdout; complete records stay on disk.
            node.body[-1] = ast.parse(
                "print(name,json.dumps({k:v for k,v in value.items() "
                "if k not in ('original_records','targets')},sort_keys=True),flush=True)"
            ).body[0]
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            name = node.targets[0].id
            if name in bindings:
                node.value = ast.parse(f"Path({str(bindings[name])!r})", mode="eval").body
            elif name == "TEMP_CEILING":
                node.value = ast.Constant(arguments.restore_mib * 1048576)
        if isinstance(node, ast.Constant) and node.value == "BATCH39-":
            node.value = arguments.case + "-"
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "borrowers":
            # Original checker, exact approved-target projection. Whole-root
            # ledger environment references are not readers of these targets.
            node.args = [ast.parse(f"Path({str(arguments.source / target)!r})", mode="eval").body
                         for target in arguments.target] + [argument for argument in node.args
                         if not (isinstance(argument, ast.Name) and argument.id == "SOURCE")]
        if isinstance(node, ast.BinOp) and isinstance(node.left, ast.Name) and node.left.id == "RESTORE":
            if isinstance(node.op, ast.Div) and isinstance(node.right, ast.Constant) and node.right.value == "output":
                node.right.value = arguments.source.name

    metadata = ast.parse(
        "permission=admit('archive')\n"
        "metadata={'epoch':time.time(),'source':str(SOURCE),'archive':str(ARCHIVE),"
        "'restore':str(RESTORE),'original_records':original,'normalized_sha256':signature,"
        "'source_allocated':source_bytes,'temporary_ceiling':TEMP_CEILING,"
        "'permission':permission,'restore_counted_once_in_admin_scratch':True}"
    ).body
    targets = ast.parse(
        "for relative in " + repr(arguments.target) + ":\n"
        " target=SOURCE/relative\n"
        " assert target.is_dir() and not target.is_symlink()\n"
        " targets.append(target)\n"
    ).body
    creator = ast.parse(CREATOR.read_text()).body
    configured = []
    in_old_admission = False
    replaced_admission = replaced_targets = replaced_restore = 0
    for node in tree.body:
        if isinstance(node, ast.Assign) and any(isinstance(target, ast.Name) and target.id == "program" for target in node.targets):
            in_old_admission = True
            configured.extend(admission + metadata)
            replaced_admission += 1
        if in_old_admission:
            if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name) and node.value.func.id == "record":
                in_old_admission = False
            else:
                continue
        if isinstance(node, ast.For) and isinstance(node.target, ast.Name) and node.target.id == "version":
            configured.extend(targets)
            replaced_targets += 1
            continue
        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute):
            call = node.value
            if isinstance(call.func.value, ast.Name) and call.func.value.id == "RESTORE" and call.func.attr == "mkdir":
                configured.extend(ast.parse("admit('restore'); RESTORE.parent.mkdir(parents=True,exist_ok=True)").body)
                configured.extend(creator)
                replaced_restore += 1
                continue
            if isinstance(call.func.value, ast.Name) and call.func.value.id == "os" and call.func.attr == "sched_setaffinity":
                # The released original process scope owns CPU placement, not
                # the recorded Batch39's obsolete literal CPU0.
                continue
        configured.append(node)
    assert (replaced_admission, replaced_targets, replaced_restore) == (1, 1, 1)
    tree.body = configured
    return ast.fix_missing_locations(tree)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("source", "archive", "restore", "receipts", "fund", "operations", "funding-receipt"):
        parser.add_argument("--" + name, required=True, type=Path)
    for name in ("slot", "case", "phase-prefix"):
        parser.add_argument("--" + name, required=True)
    parser.add_argument("--restore-mib", required=True, type=int)
    parser.add_argument("--target", action="append", required=True)
    dispatch = parser.add_mutually_exclusive_group(required=True)
    dispatch.add_argument("--prepare", type=Path, help="write selected source exclusively; no owner dispatch")
    dispatch.add_argument("--execute", action="store_true", help="execute only after separate original release")
    arguments = parser.parse_args()
    selected = configure(arguments)
    code = compile(selected, str(Path(__file__).resolve()), "exec")
    if arguments.prepare:
        with arguments.prepare.open("x") as output:
            output.write(ast.unparse(selected) + "\n")
        print(json.dumps({"consumer": str(Path(__file__).resolve()), "creator": str(CREATOR.resolve()),
                          "selected_source": str(arguments.prepare), "source": str(arguments.source),
                          "archive": str(arguments.archive), "restore": str(arguments.restore),
                          "fund": str(arguments.fund), "receipts": str(arguments.receipts),
                          "archive_or_retirement_dispatched": False}, sort_keys=True))
    else:
        arguments.receipts.mkdir(parents=True, exist_ok=True)
        exec(code, {"__file__": str(RECORDED / "batch56-admin-proof02.py")})


if __name__ == "__main__":
    main()
