"""Exercise the future creator's actual outer mkdir as root and du as ts.

This is a tiny access qualification, not another archive/retirement driver.
"""
import ast
import copy
import hashlib
import json
import os
from pathlib import Path
import pwd
import subprocess
import tempfile
import unittest


class ColdRestoreContainerTest(unittest.TestCase):
    def test_privileged_outer_creation_allows_original_ledger_reader(self):
        self.assertEqual(os.geteuid(), 0, "run via the privileged performer UID")
        repo = Path(__file__).resolve().parents[2]
        creator = repo / "scripts/blind_analysis/cold_retirement/batch39-cold-proof.py"
        original = Path(
            "/home/ts/wt/openhcs-issue-batch-20260929/"
            "neurite-development-skill383-20261001/output/resource-owner-20261002/"
            "batch39-cold-proof.py"
        )
        original_bytes = original.read_bytes()
        self.assertEqual(
            hashlib.sha256(original_bytes).hexdigest(),
            "e36daaa49eb76ae9dac4f2cf0713a7502f6638f6eae05f17e3ea70de21bb25d3",
        )
        tree = ast.parse(creator.read_text())
        creation = [
            node for node in tree.body
            if isinstance(node, ast.Expr)
            and isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Attribute)
            and isinstance(node.value.func.value, ast.Name)
            and node.value.func.value.id == "RESTORE"
            and node.value.func.attr == "mkdir"
        ]
        self.assertEqual(len(creation), 1)
        self.assertEqual(ast.literal_eval(creation[0].value.keywords[0].value), 0o755)
        normalized = copy.deepcopy(tree)
        for node in ast.walk(normalized):
            if isinstance(node, ast.Call) and ast.dump(node) == ast.dump(creation[0].value):
                node.keywords[0].value = ast.Constant(value=0o700)
        self.assertEqual(ast.dump(normalized), ast.dump(ast.parse(original_bytes)))

        reader = pwd.getpwnam("ts")
        with tempfile.TemporaryDirectory(prefix="cold-restore-access-", dir=repo / "validation") as temporary:
            workspace = Path(temporary)
            # Only the new test workspace models the declared ts0755 parent.
            os.chown(workspace, reader.pw_uid, reader.pw_gid)
            os.chmod(workspace, 0o755)
            restore = workspace / "restore"
            exec(compile(ast.Module(body=creation, type_ignores=[]), str(creator), "exec"), {"RESTORE": restore})
            self.assertEqual((restore.stat().st_uid, restore.stat().st_mode & 0o7777), (0, 0o755))
            inner = restore / "output"
            inner.mkdir(mode=0o700)
            os.chown(inner, reader.pw_uid, reader.pw_gid)
            payload = inner / "proof.txt"
            payload.write_bytes(b"inner archive bytes stay unchanged\n")
            os.chown(payload, reader.pw_uid, reader.pw_gid)

            def inner_metadata():
                return [
                    (path.name, path.stat().st_mode, path.stat().st_uid,
                     path.stat().st_gid, path.stat().st_mtime_ns,
                     path.read_bytes() if path.is_file() else None)
                    for path in (inner, payload)
                ]

            before = inner_metadata()
            result = subprocess.run(
                ["sudo", "-n", "-u", "ts", "du", "-s", "-B1", str(workspace)],
                capture_output=True, text=True,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stderr, "")
            self.assertEqual(inner_metadata(), before)
            print(json.dumps({
                "effective_creator_uid": os.geteuid(),
                "ledger_reader_uid": reader.pw_uid,
                "outer_uid": restore.stat().st_uid,
                "outer_mode": oct(restore.stat().st_mode & 0o7777),
                "inner_mode": oct(inner.stat().st_mode & 0o7777),
                "inner_metadata_and_bytes_unchanged": True,
                "ts_du_returncode": result.returncode,
                "ts_du_stdout": result.stdout.strip(),
                "original_ast_except_outer_mode_unchanged": True,
            }, sort_keys=True), flush=True)


if __name__ == "__main__":
    unittest.main()
