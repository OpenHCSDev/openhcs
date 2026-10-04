"""Actual future Batch56 invocation, root creator and original ts reader."""
import ast
import hashlib
import json
import os
from pathlib import Path
import pwd
import runpy
import subprocess
import tempfile
import unittest


class ColdRestoreContainerTest(unittest.TestCase):
    def test_selected_consumer_and_original_ledger_reader(self):
        self.assertEqual(os.geteuid(), 0)
        repo = Path(__file__).resolve().parents[2]
        consumer = repo / "scripts/blind_analysis/cold_retirement/batch56-admin-proof.py"
        creator = consumer.with_name("restore_creator.py")
        recorded = runpy.run_path(str(consumer))["RECORDED"]
        for name, sha in (
            ("batch39-cold-proof.py", "e36daaa49eb76ae9dac4f2cf0713a7502f6638f6eae05f17e3ea70de21bb25d3"),
            ("batch36-xz02-proof.py", "91f515b9c65dce1eae973ab56625cc403dff95e3024d9b485c613dc3aaafb919"),
            ("batch56-admin-proof02.py", "b18ae210c9eba5281bbc8b08998352dc6f48e12298e0a0ebfc4895a0ec39be83"),
        ):
            self.assertEqual(hashlib.sha256((recorded / name).read_bytes()).hexdigest(), sha)
        reader = pwd.getpwnam("ts")
        with tempfile.TemporaryDirectory(prefix="cold-restore-access-", dir=repo / "validation") as temporary:
            workspace = Path(temporary)
            os.chown(workspace, reader.pw_uid, reader.pw_gid)
            os.chmod(workspace, 0o755)
            prepared = workspace / "selected.py"
            command = ["/usr/bin/python", "-B", str(consumer)]
            paths = {"source": workspace / "new-source", "archive": workspace / "new-archive.tar.xz",
                     "restore": workspace / "restore", "receipts": workspace / "new-receipts",
                     "fund": workspace / "new-FUND", "funding-receipt": workspace / "new-release.disk",
                     "operations": repo / "scripts/blind_analysis/operations"}
            for name, value in paths.items():
                command.extend(["--" + name, str(value)])
            command.extend(["--slot", "ADMIN_NEXT", "--case", "NEXT-C01", "--phase-prefix", "next_c01",
                            "--restore-mib", "320", "--target", "results", "--prepare", str(prepared)])
            result = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            selection = json.loads(result.stdout)
            self.assertEqual(selection["creator"], str(creator))
            self.assertFalse(selection["archive_or_retirement_dispatched"])
            self.assertFalse(paths["source"].exists())
            self.assertFalse(paths["archive"].exists())
            tree = ast.parse(prepared.read_text())
            bindings = {node.targets[0].id: ast.literal_eval(node.value.args[0]) for node in tree.body
                        if isinstance(node, ast.Assign) and len(node.targets) == 1
                        and isinstance(node.targets[0], ast.Name) and isinstance(node.value, ast.Call)
                        and isinstance(node.value.func, ast.Name) and node.value.func.id == "Path"}
            for name, key in (("SOURCE", "source"), ("ARCHIVE", "archive"), ("RESTORE", "restore"),
                              ("RECEIPTS", "receipts"), ("FUNDING", "funding-receipt")):
                self.assertEqual(bindings[name], str(paths[key]))
            self.assertEqual(bindings["proof"], str(recorded / "batch36-xz02-proof.py"))
            scans = [node for node in ast.walk(tree) if isinstance(node, ast.Call)
                     and isinstance(node.func, ast.Name) and node.func.id == "borrowers"]
            self.assertEqual(len(scans), 2)
            for scan in scans:
                self.assertEqual(ast.literal_eval(scan.args[0].args[0]), str(paths["source"] / "results"))
                self.assertFalse(any(isinstance(arg, ast.Name) and arg.id == "SOURCE" for arg in scan.args))
            admission = next(node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == "admit")
            routed = next(node for node in ast.walk(admission) if isinstance(node, ast.List))
            command = [eval(compile(ast.Expression(item), "<route>", "eval"), {"phase": "qualified_stage"})
                       for item in routed.elts]
            script, fund, slot, phase, mode = command[command.index("bash") + 1:]
            self.assertEqual(script, str(paths["operations"] / "resource-check.sh"))
            self.assertEqual(fund, str(paths["fund"]))
            self.assertEqual((slot, phase, mode), ("ADMIN_NEXT", "qualified_stage", "ongoing"))
            creation = [node for node in tree.body if isinstance(node, ast.Expr)
                        and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute)
                        and isinstance(node.value.func.value, ast.Name)
                        and node.value.func.value.id == "RESTORE" and node.value.func.attr == "mkdir"]
            self.assertEqual(len(creation), 1)
            self.assertEqual(ast.dump(creation[0]), ast.dump(ast.parse(creator.read_text()).body[0]))
            restore = paths["restore"]
            exec(compile(ast.Module(body=creation, type_ignores=[]), str(prepared), "exec"), {"RESTORE": restore})
            self.assertEqual((restore.stat().st_uid, restore.stat().st_mode & 0o7777), (0, 0o755))
            inner = restore / "output"
            inner.mkdir(mode=0o700)
            os.chown(inner, reader.pw_uid, reader.pw_gid)
            payload = inner / "proof.txt"
            payload.write_bytes(b"inner archive bytes stay unchanged\n")
            os.chown(payload, reader.pw_uid, reader.pw_gid)

            def metadata():
                return [(p.stat().st_mode, p.stat().st_uid, p.stat().st_gid, p.stat().st_mtime_ns,
                         p.read_bytes() if p.is_file() else None) for p in (inner, payload)]

            before = metadata()
            du = subprocess.run(["sudo", "-n", "-u", "ts", "du", "-s", "-B1", str(workspace)], capture_output=True, text=True)
            self.assertEqual((du.returncode, du.stderr), (0, ""))
            self.assertEqual(metadata(), before)
            print(json.dumps({"actual_consumer_prepare_returncode": result.returncode,
                              "selected_creator": selection["creator"], "old_destructive_defaults_replaced": True,
                              "archive_or_retirement_dispatched": False, "ts_du_returncode": du.returncode,
                              "outer_mode": "0o755", "inner_mode": "0o700",
                              "inner_metadata_and_bytes_unchanged": True}, sort_keys=True), flush=True)


if __name__ == "__main__":
    unittest.main()
