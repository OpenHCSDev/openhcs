"""Exercise ordinary installed policy and actual read-only namespace, not a mock."""

import errno
import os
import sys
from pathlib import Path

from openhcs.agent.path_policy import AgentPathPolicy, AgentPathPolicyError

image = Path(sys.argv[1])
parent = Path(sys.argv[2])
policy = AgentPathPolicy.from_environment()
admitted = policy.assert_readable(image)
with admitted.open("rb") as source:
    header = source.read(16)
assert header[:2] in (b"II", b"MM"), header
try:
    policy.assert_writable(image)
except AgentPathPolicyError:
    print("PASS ordinary installed AgentPathPolicy: saved mosaic readable, write denied")
else:
    raise AssertionError("ancestor admitted as writable")
try:
    descriptor = os.open(image, os.O_WRONLY)
except OSError as error:
    assert error.errno == errno.EROFS, error
    print("PASS actual bwrap namespace: ancestor HDD opened read-only")
else:
    os.close(descriptor)
    raise AssertionError("read-only bind admitted a writer")
for foreign in (parent / "H004_HDD_96/author-workspace/output", Path("/run/media/ts/hdd")):
    try:
        policy.assert_readable_location(foreign)
    except AgentPathPolicyError:
        pass
    else:
        raise AssertionError(f"foreign or broad HDD root admitted: {foreign}")
print("PASS sibling artifacts and general HDD root denied")
policy.assert_writable(Path(__file__).parent / "new-phase-output")
print("PASS new owned phase remains writable under ordinary policy")
