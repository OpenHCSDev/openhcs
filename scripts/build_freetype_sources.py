"""Derive the private font-engine build from FreeType's upstream declarations."""

import re
from pathlib import Path


def freetype_sources(root: Path) -> list[str]:
    configuration = (root / "modules.cfg").read_text()
    modules = re.findall(
        r"^(?:FONT|HINTING|RASTER|AUX)_MODULES\s*\+=\s*(\w+)\s*$",
        configuration, re.MULTILINE,
    )
    sources = []
    for module in ["base", *modules]:
        rules = (root / "src" / module / "rules.mk").read_text()
        aggregate = re.findall(
            r"^\w+_SRC_S\s*:=\s*\$\(\w+_DIR\)/(\w+\.c)\s*$",
            rules, re.MULTILINE,
        )
        if not aggregate:
            aggregate = re.findall(
                r"^\w+_DRV_SRC\s*:=\s*\$\(\w+_DIR\)/(\w+\.c)\s*$",
                rules, re.MULTILINE,
            )
        if len(aggregate) != 1:
            raise ValueError(f"Unsupported FreeType aggregate declaration: {module}")
        sources.append(root / "src" / module / aggregate[0])
    core = (root / "builds" / "freetype.mk").read_text()
    sources.extend(root / "src" / "base" / name for name in re.findall(
        r"^FT(?:SYS|DEBUG|INIT)_SRC\s*[:?]=\s*\$\(BASE_DIR\)/(\w+\.c)\s*$",
        core, re.MULTILINE,
    ))
    sources.extend(root / "src" / "base" / name for name in re.findall(
        r"^BASE_EXTENSIONS\s*\+=\s*(\w+\.c)\s*$",
        configuration, re.MULTILINE,
    ))
    if not all(path.is_file() for path in sources):
        raise ValueError("FreeType declaration references a missing packaged source")
    return [str(path) for path in sources]
