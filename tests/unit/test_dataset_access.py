"""Whether a dataset initializes in place is the filesystem's answer.

The non-writable case (POSIX mode bits, Windows ACLs) is exercised by the
read-only integration journeys, which make a genuinely non-writable tree.
"""

from pathlib import Path

from openhcs.authoring.session.session import UnrestrictedDatasetAccess


def test_writable_root_initializes_in_place_and_the_probe_leaves_nothing(
    tmp_path: Path,
) -> None:
    (tmp_path / "image.tif").write_bytes(b"pixels")

    assert UnrestrictedDatasetAccess().initializes_in_place(tmp_path)
    assert [path.name for path in tmp_path.iterdir()] == ["image.tif"]


def test_missing_root_does_not_initialize_in_place(tmp_path: Path) -> None:
    assert not UnrestrictedDatasetAccess().initializes_in_place(tmp_path / "absent")
