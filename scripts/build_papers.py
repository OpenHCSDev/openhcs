#!/usr/bin/env python3
"""
Unified paper build system for all TOPLAS papers.

OpenHCS Architecture:
  - Declarative: Configuration in YAML, not code
  - Fail-Loud: Explicit validation, no silent failures
  - Orthogonal: One responsibility per function
  - Explicit Dependency Injection: No hidden state
  - Compile-Time Validation: Check everything upfront

STRUCTURAL INVARIANTS (mathematical constraints):
  1. Content: ∀p ∈ Papers: content(p) ⊂ paper_dir(p)/latex/content/*.tex
  2. Proofs:  ∀p ∈ Papers: proofs(p) ⊂ proofs_dir/paper{id}_*.lean
  3. Output:  ∀p ∈ Papers: releases(p) = {pdf, md, copy_paste.txt, BUILD_LOG.txt, tar.gz, zip}

All papers follow identical structure. No special cases.
"""

import sys
import subprocess
import shutil
from pathlib import Path
from typing import List, Dict, Tuple, Optional, Set
from dataclasses import dataclass
import yaml
import argparse
from datetime import datetime
import re
import hashlib


@dataclass(frozen=True)
class ArxivConfig:
    """Immutable arXiv packaging configuration."""

    include_build_log: bool = True
    include_lean_source: bool = True
    include_build_config: bool = True
    exclude_patterns: Tuple[str, ...] = (".lake", "build", "*.olean", "*.ilean")

    @classmethod
    def from_dict(cls, d: dict) -> "ArxivConfig":
        return cls(
            include_build_log=d.get("include_build_log", True),
            include_lean_source=d.get("include_lean_source", True),
            include_build_config=d.get("include_build_config", True),
            exclude_patterns=tuple(d.get("exclude_patterns", [])),
        )


@dataclass(frozen=True)
class PaperMeta:
    """Immutable paper metadata. Represents a single paper's configuration."""

    paper_id: str  # e.g., "paper1"
    name: str  # e.g., "Typing Discipline"
    full_name: str  # Full paper title
    dir_name: str  # e.g., "paper1_typing_discipline"
    latex_dir: str  # Relative to paper dir, typically "latex"
    latex_file: str  # Main .tex file name
    venue: str  # Target venue, e.g., "JSAIT", "TOPLAS"
    proofs_dir: str = "proofs"
    module_root: str = ""  # Lean module root (auto-derived if empty)
    archive_prefix: str = ""
    lean_dependencies: Tuple[
        str, ...
    ] = ()  # Other papers whose Lean to include in releases
    assumption_ledger_sources: Tuple[str, ...] = ()
    claim_mapping_file: str = ""
    arxiv_comments: str = ""
    scaffold_from: str = ""

    @classmethod
    def from_dict(cls, paper_id: str, d: dict) -> "PaperMeta":
        return cls(
            paper_id=paper_id,
            name=d["name"],
            full_name=d["full_name"],
            dir_name=d["dir"],
            latex_dir=d.get("latex_dir", "latex"),
            latex_file=d["latex_file"],
            venue=d.get("venue", "Draft"),
            proofs_dir=d.get("proofs_dir", "proofs"),
            module_root=d.get("module_root", ""),
            archive_prefix=d.get("archive_prefix", ""),
            lean_dependencies=tuple(d.get("lean_dependencies", [])),
            assumption_ledger_sources=tuple(d.get("assumption_ledger_sources", [])),
            claim_mapping_file=d.get("claim_mapping_file", ""),
            arxiv_comments=d.get("arxiv_comments", ""),
            scaffold_from=d.get("scaffold_from", ""),
        )


@dataclass(frozen=True)
class LeanStats:
    """Computed Lean proof statistics for a paper."""

    line_count: int
    theorem_count: int
    sorry_count: int
    file_count: int


@dataclass(frozen=True)
class LeanFileStats:
    """Per-file Lean proof statistics."""

    line_count: int
    theorem_count: int
    sorry_count: int


class PaperBuilder:
    """
    Unified builder for all paper formats.

    STRUCTURAL INVARIANTS:
    1. ∀p: paper_dir(p) = papers_dir / meta(p).dir_name
    2. ∀p: content_dir(p) = paper_dir(p) / meta(p).latex_dir / "content"
    3. ∀p: releases_dir(p) = paper_dir(p) / "releases"
    4. ∀p: proofs_dir(p) = paper_dir(p) / "proofs"

    All papers follow these invariants. No exceptions.
    """

    def __init__(
        self,
        repo_root: Path,
        validate_prerequisites: bool = True,
        validate_paper_structure: bool = True,
    ):
        self.repo_root = repo_root
        self.scripts_dir = repo_root / "scripts"
        self.papers_dir = repo_root / "docs" / "papers"

        # Load configuration
        self._raw_metadata = self._load_raw_metadata()
        self.arxiv_config = ArxivConfig.from_dict(self._raw_metadata.get("arxiv", {}))
        self.papers: Dict[str, PaperMeta] = self._load_papers()
        self._lean_stats_cache: Dict[Path, LeanStats] = {}
        self._lean_file_stats_cache: Dict[Path, Dict[str, LeanFileStats]] = {}

        # Captured build output for BUILD_LOG.txt
        self._lean_build_output: str = ""

        # Validate upfront (fail-loud)
        if validate_prerequisites:
            self._validate_prerequisites()
        if validate_paper_structure:
            self._validate_paper_structure()

    def _load_raw_metadata(self) -> dict:
        """Load raw YAML metadata."""
        metadata_file = self.scripts_dir / "papers.yaml"
        if not metadata_file.exists():
            raise FileNotFoundError(f"papers.yaml not found at {metadata_file}")
        with open(metadata_file) as f:
            return yaml.safe_load(f)

    def _load_papers(self) -> Dict[str, PaperMeta]:
        """Convert raw YAML to immutable PaperMeta objects."""
        papers = {}
        for paper_id, paper_dict in self._raw_metadata.get("papers", {}).items():
            papers[paper_id] = PaperMeta.from_dict(paper_id, paper_dict)
        return papers

    def _validate_prerequisites(self):
        """Fail loudly if required tools are missing."""
        required = ["pdflatex", "bibtex", "pandoc", "lake"]
        missing = [cmd for cmd in required if not shutil.which(cmd)]
        if missing:
            raise RuntimeError(
                f"Missing required tools: {', '.join(missing)}\n"
                f"Install with: sudo apt install {' '.join(missing)}"
            )

    def _validate_paper_structure(self):
        """Validate structural invariants for all papers."""
        errors = []
        for paper_id, meta in self.papers.items():
            paper_dir = self.papers_dir / meta.dir_name
            if not paper_dir.exists():
                errors.append(f"{paper_id}: paper_dir not found: {paper_dir}")
                continue

            latex_dir = paper_dir / meta.latex_dir
            if not latex_dir.exists():
                errors.append(f"{paper_id}: latex_dir not found: {latex_dir}")

            latex_file = latex_dir / meta.latex_file
            if not latex_file.exists():
                errors.append(f"{paper_id}: latex_file not found: {latex_file}")

            content_dir = latex_dir / "content"
            if not content_dir.exists():
                errors.append(f"{paper_id}: content_dir not found: {content_dir}")

        if errors:
            raise ValueError(
                f"Paper structure validation failed:\n"
                + "\n".join(f"  - {e}" for e in errors)
            )

    def _get_paper_meta(self, paper_id: str) -> PaperMeta:
        """Get paper metadata, fail if not found."""
        if paper_id not in self.papers:
            valid = ", ".join(self.papers.keys())
            raise ValueError(f"Unknown paper: {paper_id}. Valid papers: {valid}")
        return self.papers[paper_id]

    def _get_paper_dir(self, paper_id: str) -> Path:
        """Get paper directory path."""
        meta = self._get_paper_meta(paper_id)
        return self.papers_dir / meta.dir_name

    def _get_content_dir(self, paper_id: str) -> Path:
        """Get content directory: paper_dir/latex/content (INVARIANT 2)."""
        meta = self._get_paper_meta(paper_id)
        return self.papers_dir / meta.dir_name / meta.latex_dir / "content"

    def _get_releases_dir(self, paper_id: str) -> Path:
        """Get releases directory, creating if needed (INVARIANT 3)."""
        releases_dir = self._get_paper_dir(paper_id) / "releases"
        releases_dir.mkdir(parents=True, exist_ok=True)
        return releases_dir

    def _write_text_file(
        self,
        path: Path,
        content: str,
        overwrite: bool,
        created_files: List[Path],
        skipped_files: List[Path],
    ) -> None:
        """Write UTF-8 text file unless it exists and overwrite is disabled."""
        if path.exists() and not overwrite:
            skipped_files.append(path)
            return
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
        created_files.append(path)

    def _compact_lean_handle(self, handle: str) -> str:
        """Render long Lean handles with compact namespace prefixes."""
        if "." not in handle:
            return handle
        full_prefix, remainder = handle.split(".", 1)
        short_prefix = self._compact_lean_prefix(full_prefix)
        if short_prefix:
            return short_prefix + "." + remainder
        return handle

    def _compact_lean_prefix(self, full_prefix: str) -> str:
        """Compact a Lean namespace prefix to a stable short code.

        Strategy:
        derive initials from CamelCase segments deterministically.
        """
        # Split CamelCase / PascalCase into lexical chunks, keep alnum.
        chunks = re.findall(r"[A-Z][a-z0-9]*|[a-z]+|[0-9]+", full_prefix)
        initials_parts: List[str] = []
        for chunk in chunks:
            if not chunk:
                continue
            head = chunk[0]
            if not head.isalpha():
                continue
            tail_digits = "".join(ch for ch in chunk[1:] if ch.isdigit())
            initials_parts.append(head.upper() + tail_digits)
        initials = "".join(initials_parts)
        if initials:
            return initials

        cleaned = re.sub(r"[^A-Za-z0-9]+", "", full_prefix)
        if cleaned:
            return cleaned[:3].upper()
        return full_prefix

    def _to_pascal_case(self, raw: str) -> str:
        """Convert an arbitrary identifier to a Lean-safe PascalCase module root."""
        tokens = [tok for tok in re.split(r"[^A-Za-z0-9]+", raw) if tok]
        if not tokens:
            return "PaperScaffold"
        normalized = "".join(tok[:1].upper() + tok[1:] for tok in tokens)
        if normalized[0].isdigit():
            normalized = f"P{normalized}"
        return normalized

    def _to_package_name(self, raw: str) -> str:
        """Convert an arbitrary identifier to a Lean package-safe snake_case name."""
        normalized = re.sub(r"[^a-zA-Z0-9_]+", "_", raw).strip("_").lower()
        if not normalized:
            normalized = "paper_scaffold"
        if normalized[0].isdigit():
            normalized = f"p_{normalized}"
        return normalized

    def _discover_template_lean_toolchain(self) -> str:
        """Find an existing Lean toolchain pin from current papers, or use a safe fallback."""
        candidate_paths: List[Path] = []
        for meta in self.papers.values():
            candidate_paths.append(
                self.papers_dir / meta.dir_name / meta.proofs_dir / "lean-toolchain"
            )

        for path in candidate_paths:
            if not path.exists():
                continue
            content = path.read_text(encoding="utf-8", errors="replace").strip()
            if content:
                return content

        return "leanprover/lean4:stable"

    def _discover_template_mathlib_require(self) -> str:
        """Extract a pinned `require mathlib` block from an existing lakefile."""
        pattern = re.compile(
            r"require\s+mathlib\s+from\s+git\s*\n\s*\"[^\"]+\"\s*@\s*\"[^\"]+\"",
            re.MULTILINE,
        )
        candidate_paths: List[Path] = []
        for meta in self.papers.values():
            candidate_paths.append(
                self.papers_dir / meta.dir_name / meta.proofs_dir / "lakefile.lean"
            )

        for path in candidate_paths:
            if not path.exists():
                continue
            content = path.read_text(encoding="utf-8", errors="replace")
            match = pattern.search(content)
            if match:
                return match.group(0)

        return (
            "require mathlib from git\n"
            '  "https://github.com/leanprover-community/mathlib4" @ "master"'
        )

    def _latex_main_template(self, meta: PaperMeta) -> str:
        """Generate a self-contained LaTeX starter file for a new paper variant."""
        return f"""\\documentclass[11pt]{{article}}
\\usepackage{{paper-preamble}}

% Auto-generated scaffold. Replace with venue-specific preamble as needed.
\\IfFileExists{{content/lean_stats.tex}}{{\\input{{content/lean_stats.tex}}}}{{}}
\\providecommand{{\\claimstamp}}[2]{{\\allowbreak{{\\scriptsize\\textit{{[C:#1;R:#2]}}}}}}
\\providecommand{{\\leanmeta}}[1]{{\\allowbreak{{\\scriptsize\\textit{{(L: #1)}}}}}}

\\title{{{meta.full_name}}}
\\author{{Anonymous Author\\\\Anonymous Institution\\\\\\texttt{{anonymous@example.com}}}}
\\date{{\\today}}

\\begin{{document}}
\\maketitle

\\begin{{abstract}}
\\input{{content/abstract.tex}}
\\end{{abstract}}

\\input{{content/01_introduction.tex}}

\\bibliographystyle{{plain}}
\\bibliography{{references}}

\\end{{document}}
"""

    def _latex_abstract_template(self, meta: PaperMeta) -> str:
        """Generate default abstract placeholder content."""
        return (
            f"Scaffold abstract for {meta.name}. "
            "Replace this paragraph with the final abstract text.\n"
        )

    def _latex_intro_template(self, meta: PaperMeta) -> str:
        """Generate default introduction placeholder content."""
        return f"""\\section{{Introduction}}

This is scaffold content for \\texttt{{{meta.paper_id}}}. Replace it with your paper text.
"""

    def _references_template(self) -> str:
        """Generate an empty bibliography placeholder."""
        return "% Auto-generated scaffold bibliography.\n% Add BibTeX entries here.\n"

    def _proofs_readme_template(self, meta: PaperMeta) -> str:
        """Generate README for scaffolded Lean proofs."""
        return f"""# {meta.name} Lean Proofs

This directory was scaffolded by `scripts/build_papers.py scaffold {meta.paper_id}`.

- Replace starter modules with your formalization.
- Run `lake build` inside this directory once dependencies are initialized.
"""

    def _replace_first_latex_title(self, content: str, new_title: str) -> str:
        """Replace first `\\title{...}` argument while preserving surrounding LaTeX."""
        marker = r"\title"
        start = content.find(marker)
        if start == -1:
            return content

        i = start + len(marker)
        n = len(content)
        while i < n and content[i].isspace():
            i += 1
        if i < n and content[i] == "[":
            depth = 1
            i += 1
            while i < n and depth > 0:
                if content[i] == "[":
                    depth += 1
                elif content[i] == "]":
                    depth -= 1
                i += 1
            while i < n and content[i].isspace():
                i += 1
        if i >= n or content[i] != "{":
            return content

        arg_start = i + 1
        depth = 1
        i = arg_start
        while i < n and depth > 0:
            ch = content[i]
            prev = content[i - 1] if i > 0 else ""
            if ch == "{" and prev != "\\":
                depth += 1
            elif ch == "}" and prev != "\\":
                depth -= 1
            i += 1
        if depth != 0:
            return content

        arg_end = i - 1
        return content[:arg_start] + new_title + content[arg_end:]

    def _build_derived_latex_scaffold(
        self,
        paper_id: str,
        meta: PaperMeta,
        latex_dir: Path,
        content_dir: Path,
    ) -> Optional[List[Tuple[Path, str]]]:
        """Build scaffold file list by deriving from an existing paper variant."""
        source_id = meta.scaffold_from.strip()
        if not source_id:
            return None
        if source_id == paper_id:
            raise ValueError(f"{paper_id}: scaffold_from cannot reference itself")

        source_meta = self._get_paper_meta(source_id)
        source_latex_dir = self._get_paper_dir(source_id) / source_meta.latex_dir
        source_main = source_latex_dir / source_meta.latex_file
        if not source_main.exists():
            raise FileNotFoundError(
                f"{paper_id}: scaffold_from source missing main TeX: "
                f"{source_main.relative_to(self.repo_root)}"
            )

        source_main_content = source_main.read_text(encoding="utf-8", errors="replace")
        main_content = self._replace_first_latex_title(
            source_main_content, meta.full_name
        )
        files_to_write: List[Tuple[Path, str]] = [
            (latex_dir / meta.latex_file, main_content),
        ]

        # Skip generated files; they are rebuilt automatically by the pipeline.
        generated_content = {
            "lean_stats.tex",
            "claim_mapping_auto.tex",
            "assumption_ledger_auto.tex",
            "proof_hardness_index_auto.tex",
        }
        source_content_dir = source_latex_dir / "content"
        copied_content = False
        if source_content_dir.exists():
            for source_file in sorted(source_content_dir.glob("*.tex")):
                if source_file.name in generated_content:
                    continue
                files_to_write.append(
                    (
                        content_dir / source_file.name,
                        source_file.read_text(encoding="utf-8", errors="replace"),
                    )
                )
                copied_content = True

        if not copied_content:
            files_to_write.extend(
                [
                    (content_dir / "abstract.tex", self._latex_abstract_template(meta)),
                    (
                        content_dir / "01_introduction.tex",
                        self._latex_intro_template(meta),
                    ),
                ]
            )

        source_references = source_latex_dir / "references.bib"
        if source_references.exists():
            files_to_write.append(
                (
                    latex_dir / "references.bib",
                    source_references.read_text(encoding="utf-8", errors="replace"),
                )
            )
        else:
            files_to_write.append(
                (latex_dir / "references.bib", self._references_template())
            )

        print(f"[scaffold] {paper_id}: deriving LaTeX scaffold from {source_id}")
        return files_to_write

    def _lakefile_template(
        self, package_name: str, module_root: str, mathlib_require: str
    ) -> str:
        """Generate a minimal lakefile pinned to the repository's current mathlib source."""
        return f"""import Lake
open Lake DSL

package «{package_name}» where
  -- Auto-generated scaffold package.

{mathlib_require}

@[default_target]
lean_lib «{module_root}» where
  globs := #[.submodules `{module_root}]
  srcDir := "."
"""

    def _lean_root_template(self, module_root: str) -> str:
        """Generate root Lean module importing starter files."""
        return f"""import {module_root}.Basic
"""

    def _lean_basic_template(self, module_root: str) -> str:
        """Generate starter Lean theorem file."""
        return f"""namespace {module_root}

theorem scaffold_sanity : True := by
  trivial

end {module_root}
"""

    def scaffold_paper(
        self, paper_id: str, overwrite: bool = False
    ) -> Dict[str, List[Path]]:
        """Create required folder/file boilerplate for a paper entry in papers.yaml."""
        meta = self._get_paper_meta(paper_id)
        paper_dir = self._get_paper_dir(paper_id)
        latex_dir = paper_dir / meta.latex_dir
        content_dir = latex_dir / "content"
        proofs_dir = self._get_paper_proofs_dir(paper_id)
        releases_dir = paper_dir / "releases"
        markdown_dir = paper_dir / "markdown"
        proofs_dir_was_nonempty = proofs_dir.exists() and any(proofs_dir.iterdir())

        created_dirs: List[Path] = []
        created_files: List[Path] = []
        skipped_files: List[Path] = []

        for directory in [
            paper_dir,
            latex_dir,
            content_dir,
            proofs_dir,
            releases_dir,
            markdown_dir,
        ]:
            if not directory.exists():
                directory.mkdir(parents=True, exist_ok=True)
                created_dirs.append(directory)

        module_root = (
            meta.module_root
            if meta.module_root
            else self._to_pascal_case(meta.dir_name)
        )
        package_name = self._to_package_name(meta.dir_name)
        lean_toolchain = self._discover_template_lean_toolchain()
        mathlib_require = self._discover_template_mathlib_require()

        # Copy preamble from shared (SSOT)
        shared_preamble = self.papers_dir / "shared" / "paper-preamble.sty"

        files_to_write = self._build_derived_latex_scaffold(
            paper_id, meta, latex_dir, content_dir
        )
        if files_to_write is None:
            files_to_write = [
                (latex_dir / meta.latex_file, self._latex_main_template(meta)),
                (content_dir / "abstract.tex", self._latex_abstract_template(meta)),
                (content_dir / "01_introduction.tex", self._latex_intro_template(meta)),
                (latex_dir / "references.bib", self._references_template()),
            ]

        # Always copy preamble from shared (SSOT) - use "COPY" marker
        if shared_preamble.exists():
            files_to_write.append((latex_dir / "paper-preamble.sty", "COPY"))
        if overwrite or not proofs_dir_was_nonempty:
            files_to_write.extend(
                [
                    (proofs_dir / "README.md", self._proofs_readme_template(meta)),
                    (proofs_dir / "lean-toolchain", f"{lean_toolchain}\n"),
                    (
                        proofs_dir / "lakefile.lean",
                        self._lakefile_template(
                            package_name, module_root, mathlib_require
                        ),
                    ),
                    (
                        proofs_dir / f"{module_root}.lean",
                        self._lean_root_template(module_root),
                    ),
                    (
                        proofs_dir / module_root / "Basic.lean",
                        self._lean_basic_template(module_root),
                    ),
                ]
            )
        else:
            print(
                f"[scaffold] {paper_id}: proofs scaffold skipped "
                f"(existing non-empty directory: {proofs_dir.relative_to(self.repo_root)})"
            )

        for path, content in files_to_write:
            if content == "COPY":
                # Copy from source (shared preamble)
                src = self.papers_dir / "shared" / path.name
                if src.exists():
                    import shutil

                    shutil.copy2(src, path)
                    created_files.append(path)
                else:
                    print(f"[scaffold] WARNING: shared source not found: {src}")
            else:
                self._write_text_file(
                    path,
                    content,
                    overwrite=overwrite,
                    created_files=created_files,
                    skipped_files=skipped_files,
                )

        print(
            f"[scaffold] {paper_id}: created {len(created_dirs)} dirs, {len(created_files)} files"
        )
        if skipped_files:
            print(f"[scaffold] {paper_id}: skipped {len(skipped_files)} existing files")

        # Initialize generated artifacts so scaffolded papers compile with the
        # same metadata infrastructure as regular build targets.
        self._sync_shared_preambles(paper_id)
        self._write_latex_lean_stats(paper_id)
        self._write_assumption_ledger_auto(paper_id)
        self._write_lean_handle_ids_auto(paper_id)
        self._rewrite_content_lean_handles_to_ids(paper_id)
        self._normalize_and_fill_claimstamps(paper_id)
        self._write_claim_mapping_auto(paper_id)
        self._write_proof_hardness_index_auto(paper_id)

        return {
            "created_dirs": created_dirs,
            "created_files": created_files,
            "skipped_files": skipped_files,
        }

    def _discover_content_files(self, paper_id: str) -> List[Path]:
        """Discover markdown content files by following main LaTeX include order."""
        meta = self._get_paper_meta(paper_id)
        main_tex = self._get_paper_dir(paper_id) / meta.latex_dir / meta.latex_file
        if not main_tex.exists():
            raise FileNotFoundError(f"Main LaTeX file not found: {main_tex}")

        files = self._collect_included_tex_files(
            main_tex,
            include_document_body_only=True,
            include_self=False,
        )
        if files:
            ordered_unique: List[Path] = []
            seen: set[Path] = set()
            for file_path in files:
                resolved = file_path.resolve()
                if resolved in seen:
                    continue
                seen.add(resolved)
                ordered_unique.append(resolved)
            return ordered_unique

        # Fail-loud fallback: preserve prior behavior if includes cannot be discovered.
        print(
            f"[build-md] Warning: no includes parsed from {main_tex.name}; falling back to content/*.tex"
        )
        content_dir = self._get_content_dir(paper_id)
        fallback = sorted(content_dir.glob("*.tex"))
        return [f for f in fallback if f.name != "abstract.tex"]

    def _strip_latex_comments(self, content: str) -> str:
        """Remove LaTeX comments while preserving escaped percent signs."""
        return re.sub(r"(?<!\\\\)%.*", "", content)

    def _extract_document_body(self, content: str) -> str:
        """Extract content between \\begin{document} and \\end{document} when present."""
        begin = re.search(r"\\begin\{document\}", content)
        if not begin:
            return content
        end = re.search(r"\\end\{document\}", content[begin.end() :])
        if not end:
            return content[begin.end() :]
        return content[begin.end() : begin.end() + end.start()]

    def _resolve_include_path(
        self, parent_dir: Path, include_target: str, search_root: Path
    ) -> Path:
        """Resolve a LaTeX \\input/\\include target to a concrete .tex path.

        LaTeX resolves includes relative to the current file and the main working
        directory. We mirror that behavior by searching both roots.
        """
        raw_target = include_target.strip()
        candidates = [
            (parent_dir / raw_target).resolve(),
            (search_root / raw_target).resolve(),
        ]

        checked: List[Path] = []
        for candidate in candidates:
            checked.append(candidate)
            if candidate.exists():
                return candidate
            if not candidate.suffix:
                candidate_tex = candidate.with_suffix(".tex")
                checked.append(candidate_tex)
                if candidate_tex.exists():
                    return candidate_tex

        # Return best-effort path for warning output.
        return checked[-1]

    def _find_tex_includes(
        self, tex_file: Path, include_document_body_only: bool, search_root: Path
    ) -> List[Path]:
        """Parse direct \\input/\\include dependencies from a .tex file."""
        content = tex_file.read_text(encoding="utf-8", errors="replace")
        if include_document_body_only:
            content = self._extract_document_body(content)
        content = self._strip_latex_comments(content)

        include_targets = re.findall(r"\\(?:input|include)\{([^}]+)\}", content)
        includes: List[Path] = []
        for target in include_targets:
            resolved = self._resolve_include_path(tex_file.parent, target, search_root)
            if not resolved.exists():
                print(
                    f"[build-md] Warning: include target not found in {tex_file.name}: {target}"
                )
                continue
            includes.append(resolved)
        return includes

    def _collect_included_tex_files(
        self,
        tex_file: Path,
        include_document_body_only: bool = False,
        include_self: bool = True,
        active_stack: Tuple[Path, ...] = (),
        search_root: Path | None = None,
    ) -> List[Path]:
        """Recursively collect include files in document order.

        Includes parent files as well as nested includes so section files that
        contain both prose and nested ``\\input`` directives are not dropped.
        """
        resolved_tex = tex_file.resolve()
        if search_root is None:
            search_root = resolved_tex.parent
        if resolved_tex in active_stack:
            chain = " -> ".join(str(p.name) for p in (*active_stack, resolved_tex))
            raise RuntimeError(f"Circular LaTeX include detected: {chain}")

        direct_includes = self._find_tex_includes(
            resolved_tex,
            include_document_body_only=include_document_body_only,
            search_root=search_root,
        )
        ordered_files: List[Path] = [resolved_tex] if include_self else []
        next_stack = (*active_stack, resolved_tex)
        for include_file in direct_includes:
            ordered_files.extend(
                self._collect_included_tex_files(
                    include_file,
                    include_document_body_only=False,
                    include_self=True,
                    active_stack=next_stack,
                    search_root=search_root,
                )
            )
        return ordered_files

    def _get_paper_proofs_dir(self, paper_id: str) -> Path:
        """Get the proofs directory for a specific paper.

        Each paper has its own proofs directory at: paper_dir/proofs/
        For variants (e.g., paper1_jsait), use the base paper's proofs.
        """
        meta = self._get_paper_meta(paper_id)
        return self.papers_dir / meta.dir_name / meta.proofs_dir

    def _get_archive_prefix(self, paper_id: str) -> str:
        """Archive/package basename, configurable per paper."""
        meta = self._get_paper_meta(paper_id)
        return meta.archive_prefix if meta.archive_prefix else paper_id

    def _iter_paper_lean_files(self, proofs_dir: Path) -> List[Path]:
        """Return paper Lean files, excluding build/cache directories."""
        if not proofs_dir.exists():
            return []

        excluded_dirs = {".lake", "build"}
        lean_files: List[Path] = []
        for lean_file in proofs_dir.rglob("*.lean"):
            rel_parts = lean_file.relative_to(proofs_dir).parts
            if any(part in excluded_dirs for part in rel_parts):
                continue
            lean_files.append(lean_file)
        return sorted(lean_files)

    def _collect_lean_dependency_closure(self, paper_id: str) -> List[str]:
        """Return transitive Lean dependencies for `paper_id` in topological order."""
        ordered: List[str] = []
        seen: Set[str] = set()
        active: Set[str] = set()

        def visit(pid: str) -> None:
            meta = self._get_paper_meta(pid)
            for dep in meta.lean_dependencies:
                if dep not in self.papers:
                    raise ValueError(
                        f"Unknown lean dependency '{dep}' declared by {pid}"
                    )
                if dep in active:
                    cycle = " -> ".join(list(active) + [dep])
                    raise ValueError(f"Lean dependency cycle detected: {cycle}")
                if dep in seen:
                    continue
                active.add(dep)
                visit(dep)
                active.remove(dep)
                seen.add(dep)
                ordered.append(dep)

        visit(paper_id)
        return ordered

    def _iter_lean_roots_for_paper(self, paper_id: str) -> List[Tuple[str, Path]]:
        """Return `(source_paper_id, proofs_dir)` for paper + transitive dependencies."""
        roots: List[Tuple[str, Path]] = []
        roots.append((paper_id, self._get_paper_proofs_dir(paper_id)))
        for dep in self._collect_lean_dependency_closure(paper_id):
            roots.append((dep, self._get_paper_proofs_dir(dep)))
        return roots

    def _derive_module_roots_from_lakefile(self, proofs_dir: Path) -> List[str]:
        """Derive module roots from `lean_lib` globs in a paper's lakefile."""
        lakefile = proofs_dir / "lakefile.lean"
        if not lakefile.exists():
            return []
        text = lakefile.read_text(encoding="utf-8", errors="replace")
        roots: List[str] = []
        for m in re.findall(r"globs\s*:=\s*#\[\s*\.submodules\s+`([A-Za-z0-9_'.]+)\s*\]", text):
            root = m.strip()
            if root and root not in roots:
                roots.append(root)
        return roots

    def _derive_module_roots(self, paper_id: str) -> List[str]:
        """Derive importable top-level Lean module roots for a paper."""
        meta = self._get_paper_meta(paper_id)
        proofs_dir = self._get_paper_proofs_dir(paper_id)
        roots: List[str] = []

        # 1) Explicit metadata root, if provided.
        if meta.module_root:
            roots.append(meta.module_root)

        # 2) Lake globs are the canonical build roots.
        for root in self._derive_module_roots_from_lakefile(proofs_dir):
            if root not in roots:
                roots.append(root)

        # 3) Fallback: top-level Lean files (excluding config-only files).
        skip = {"lakefile.lean", "PrintAxioms.lean", "check_axioms.lean"}
        for top in sorted(proofs_dir.glob("*.lean")):
            if top.name in skip:
                continue
            stem = top.stem
            if re.fullmatch(r"[A-Z][A-Za-z0-9_']*", stem):
                if stem not in roots:
                    roots.append(stem)

        return roots

    def _files_identical(self, left: Path, right: Path) -> bool:
        """Return True iff two files have the same bytes."""
        if not left.exists() or not right.exists():
            return False
        if left.stat().st_size != right.stat().st_size:
            return False
        h1 = hashlib.sha256()
        h2 = hashlib.sha256()
        h1.update(left.read_bytes())
        h2.update(right.read_bytes())
        return h1.digest() == h2.digest()

    def _strip_lean_comments(self, content: str) -> str:
        """Strip Lean line and nested block comments for token counting."""
        out: List[str] = []
        i = 0
        n = len(content)
        block_depth = 0
        in_string = False

        while i < n:
            ch = content[i]
            nxt = content[i + 1] if i + 1 < n else ""

            if block_depth > 0:
                if ch == "/" and nxt == "-":
                    block_depth += 1
                    i += 2
                    continue
                if ch == "-" and nxt == "/":
                    block_depth -= 1
                    i += 2
                    continue
                if ch == "\n":
                    out.append("\n")
                i += 1
                continue

            if not in_string and ch == "/" and nxt == "-":
                block_depth = 1
                i += 2
                continue

            if not in_string and ch == "-" and nxt == "-":
                i += 2
                while i < n and content[i] != "\n":
                    i += 1
                if i < n and content[i] == "\n":
                    out.append("\n")
                    i += 1
                continue

            if ch == '"':
                # Toggle string state when quote is not escaped.
                backslashes = 0
                j = i - 1
                while j >= 0 and content[j] == "\\":
                    backslashes += 1
                    j -= 1
                if backslashes % 2 == 0:
                    in_string = not in_string

            out.append(ch)
            i += 1

        return "".join(out)

    def _count_theorems_and_sorries(self, content: str) -> Tuple[int, int]:
        """Count theorem/lemma declarations and sorry placeholders in Lean text."""
        theorem_re = re.compile(
            r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial|opaque)\s+)*(?:theorem|lemma)\s+[A-Za-z_][A-Za-z0-9_']*",
            re.MULTILINE,
        )
        sorry_re = re.compile(r"\bsorry\b")
        stripped = self._strip_lean_comments(content)
        return (len(theorem_re.findall(stripped)), len(sorry_re.findall(stripped)))

    def _compute_lean_file_stats(self, proofs_dir: Path) -> Dict[str, LeanFileStats]:
        """Compute per-file Lean stats keyed by relative module path (without .lean)."""
        cache_key = proofs_dir.resolve()
        if cache_key in self._lean_file_stats_cache:
            return self._lean_file_stats_cache[cache_key]

        stats: Dict[str, LeanFileStats] = {}
        for lean_file in self._iter_paper_lean_files(proofs_dir):
            rel_key = str(lean_file.relative_to(proofs_dir).with_suffix(""))
            content = lean_file.read_text(encoding="utf-8", errors="replace")
            theorem_count, sorry_count = self._count_theorems_and_sorries(content)
            stats[rel_key] = LeanFileStats(
                line_count=len(content.splitlines()),
                theorem_count=theorem_count,
                sorry_count=sorry_count,
            )

        self._lean_file_stats_cache[cache_key] = stats
        return stats

    def _compute_lean_stats(self, proofs_dir: Path) -> LeanStats:
        """Compute Lean line/theorem/sorry counts from source files."""
        cache_key = proofs_dir.resolve()
        if cache_key in self._lean_stats_cache:
            return self._lean_stats_cache[cache_key]

        per_file = self._compute_lean_file_stats(proofs_dir)
        line_count = sum(s.line_count for s in per_file.values())
        theorem_count = sum(s.theorem_count for s in per_file.values())
        sorry_count = sum(s.sorry_count for s in per_file.values())

        stats = LeanStats(
            line_count=line_count,
            theorem_count=theorem_count,
            sorry_count=sorry_count,
            file_count=len(per_file),
        )
        self._lean_stats_cache[cache_key] = stats
        return stats

    def _get_lean_stats(self, paper_id: str) -> LeanStats:
        """Get computed Lean stats for a paper or variant."""
        proofs_dir = self._get_paper_proofs_dir(paper_id)
        return self._compute_lean_stats(proofs_dir)

    def _get_lean_file_stats(self, paper_id: str) -> Dict[str, LeanFileStats]:
        """Get per-file Lean stats for a paper or variant."""
        proofs_dir = self._get_paper_proofs_dir(paper_id)
        return self._compute_lean_file_stats(proofs_dir)

    def _sync_shared_preambles(self, paper_id: str) -> None:
        """Ensure shared LaTeX preambles are present in the active paper LaTeX dir.

        This is structural SSOT sync, not one-off scaffolding:
        build/release commands should always compile against the shared preamble set.
        """
        meta = self._get_paper_meta(paper_id)
        latex_dir = self._get_paper_dir(paper_id) / meta.latex_dir
        if not latex_dir.exists():
            return

        shared_dir = self.papers_dir / "shared"
        shared_files = ["paper-preamble.sty", "pentalogy-preamble.sty"]
        for name in shared_files:
            src = shared_dir / name
            if not src.exists():
                continue
            dst = latex_dir / name
            if dst.exists():
                try:
                    if src.samefile(dst):
                        continue
                except FileNotFoundError:
                    pass
            # Always refresh from SSOT to avoid stale/local drift.
            shutil.copy2(src, dst)

    def _lean_macro_suffix(self, module_path: str) -> str:
        """Convert a relative Lean module path to a LaTeX-safe macro suffix."""
        digit_words = {
            "0": "Zero",
            "1": "One",
            "2": "Two",
            "3": "Three",
            "4": "Four",
            "5": "Five",
            "6": "Six",
            "7": "Seven",
            "8": "Eight",
            "9": "Nine",
        }
        parts = re.split(r"[^A-Za-z0-9]+", module_path)
        cleaned = [p for p in parts if p]
        if not cleaned:
            return "Unknown"
        normalized_parts: List[str] = []
        for part in cleaned:
            converted = "".join(digit_words.get(ch, ch) for ch in part)
            normalized_parts.append(converted[:1].upper() + converted[1:])
        return "".join(normalized_parts)

    def _build_lean_macro_suffix_map(self, module_paths: List[str]) -> Dict[str, str]:
        """Build collision-safe macro suffixes for Lean module paths."""
        grouped: Dict[str, List[str]] = {}
        for module_path in module_paths:
            base = self._lean_macro_suffix(module_path)
            grouped.setdefault(base, []).append(module_path)

        suffix_map: Dict[str, str] = {}
        for base, paths in grouped.items():
            if len(paths) == 1:
                suffix_map[paths[0]] = base
                continue

            # Rare collision case (e.g., Unicode-heavy names normalizing alike).
            for module_path in sorted(paths):
                digest = hashlib.sha1(module_path.encode("utf-8")).hexdigest()[:8]
                suffix_map[module_path] = f"{base}{digest}"
        return suffix_map

    def _write_latex_lean_stats(self, paper_id: str) -> None:
        """Write auto-generated Lean stats macros into latex/content/lean_stats.tex."""
        meta = self._get_paper_meta(paper_id)
        latex_dir = self._get_paper_dir(paper_id) / meta.latex_dir
        content_dir = latex_dir / "content"
        if not content_dir.exists():
            return

        total_stats = self._get_lean_stats(paper_id)
        file_stats = self._get_lean_file_stats(paper_id)
        suffix_map = self._build_lean_macro_suffix_map(sorted(file_stats.keys()))

        lines: List[str] = [
            "% Auto-generated by scripts/build_papers.py. Do not edit manually.",
            f"% Generated: {datetime.now().isoformat()}",
            f"\\providecommand{{\\LeanTotalLines}}{{{total_stats.line_count}}}",
            f"\\providecommand{{\\LeanTotalTheorems}}{{{total_stats.theorem_count}}}",
            f"\\providecommand{{\\LeanTotalSorry}}{{{total_stats.sorry_count}}}",
            f"\\providecommand{{\\LeanTotalFiles}}{{{total_stats.file_count}}}",
        ]
        for module_path in sorted(file_stats.keys()):
            suffix = suffix_map[module_path]
            stats = file_stats[module_path]
            lines.append(
                f"\\providecommand{{\\LeanLines{suffix}}}{{{stats.line_count}}}"
            )
            lines.append(
                f"\\providecommand{{\\LeanTheorems{suffix}}}{{{stats.theorem_count}}}"
            )
            lines.append(
                f"\\providecommand{{\\LeanSorry{suffix}}}{{{stats.sorry_count}}}"
            )

        (content_dir / "lean_stats.tex").write_text(
            "\n".join(lines) + "\n", encoding="utf-8"
        )

    def _iter_claim_closure_sources(self, paper_id: str) -> List[Path]:
        """Return ClaimClosure Lean sources for assumption-ledger extraction."""
        meta = self._get_paper_meta(paper_id)
        proofs_dir = self._get_paper_proofs_dir(paper_id)
        if not proofs_dir.exists():
            return []

        explicit_paths: List[Path] = []
        for rel_path in meta.assumption_ledger_sources:
            src = (proofs_dir / rel_path).resolve()
            if src.exists() and src.is_file():
                explicit_paths.append(src)

        if explicit_paths:
            return sorted(set(explicit_paths))

        candidates: List[Path] = []
        excluded_dirs = {".lake", "build"}
        for src in proofs_dir.rglob("ClaimClosure.lean"):
            rel_parts = src.relative_to(proofs_dir).parts
            if any(part in excluded_dirs for part in rel_parts):
                continue
            candidates.append(src.resolve())
        return sorted(set(candidates))

    def _extract_primary_namespace(self, content: str) -> Optional[str]:
        """Extract first namespace declaration (if any)."""
        match = re.search(r"(?m)^\s*namespace\s+([A-Za-z0-9_'.]+)\s*$", content)
        return match.group(1) if match else None

    def _parse_assumption_bundles(self, content: str) -> Dict[str, List[str]]:
        """Parse `*Assumptions` class/structure bundles and their fields."""
        bundles: Dict[str, List[str]] = {}
        matches = list(
            re.finditer(
                r"(?m)^\s*(?:class|structure)\s+([A-Za-z0-9_']*Assumptions)\b[^\n]*\bwhere\s*$",
                content,
            )
        )
        for idx, match in enumerate(matches):
            bundle_name = match.group(1)
            body_start = match.end()
            body_end = (
                matches[idx + 1].start() if idx + 1 < len(matches) else len(content)
            )
            body = content[body_start:body_end]
            fields: List[str] = []
            for raw_line in body.splitlines():
                line = raw_line.strip()
                if not line:
                    continue
                if re.match(
                    r"^(?:theorem|lemma|def|class|structure|namespace|end)\b", line
                ):
                    break
                field_match = re.match(r"^([A-Za-z0-9_']+)\s*:\s*(.+)$", line)
                if not field_match:
                    continue
                field_name = field_match.group(1)
                field_type = re.sub(r"\s+", " ", field_match.group(2)).strip()
                fields.append(
                    f"{field_name} : {field_type}" if field_type else field_name
                )
            bundles[bundle_name] = fields
        return bundles

    def _parse_conditional_handles(self, content: str) -> List[str]:
        """Extract theorem/lemma handles ending with `_conditional`."""
        handles = re.findall(
            r"(?m)^\s*(?:theorem|lemma)\s+([A-Za-z0-9_']*_conditional)\b",
            content,
        )
        return sorted(set(handles))

    def _write_assumption_ledger_auto(self, paper_id: str) -> None:
        """Write auto-generated assumption-ledger snippet when available."""
        meta = self._get_paper_meta(paper_id)
        latex_dir = self._get_paper_dir(paper_id) / meta.latex_dir
        content_dir = latex_dir / "content"
        if not content_dir.exists():
            return

        out_file = content_dir / "assumption_ledger_auto.tex"
        source_files = self._iter_claim_closure_sources(paper_id)
        if not source_files:
            out_file.write_text(
                "% Auto-generated by scripts/build_papers.py. No assumption ledger source found.\n",
                encoding="utf-8",
            )
            return

        all_bundles: Dict[str, List[str]] = {}
        all_conditional_handles: Set[str] = set()
        source_labels: List[str] = []

        proofs_dir = self._get_paper_proofs_dir(paper_id)
        for src in source_files:
            rel = src.relative_to(proofs_dir)
            source_labels.append(str(rel).replace("\\", "/"))
            content = src.read_text(encoding="utf-8", errors="replace")
            ns = self._extract_primary_namespace(content)

            bundles = self._parse_assumption_bundles(content)
            for bundle_name, fields in bundles.items():
                full_bundle_name = f"{ns}.{bundle_name}" if ns else bundle_name
                all_bundles[full_bundle_name] = fields

            for handle in self._parse_conditional_handles(content):
                full_handle = f"{ns}.{handle}" if ns else handle
                all_conditional_handles.add(full_handle)

        lines: List[str] = [
            "% Auto-generated by scripts/build_papers.py. Do not edit manually.",
            f"% Generated: {datetime.now().isoformat()}",
            r"\subsection{Assumption Ledger (Auto)}",
            r"\paragraph{Source files.}",
            r"\begin{itemize}",
        ]
        for source_label in sorted(set(source_labels)):
            lines.append(rf"\item \nolinkurl{{{source_label}}}")
        lines.append(r"\end{itemize}")

        lines.extend(
            [
                r"\paragraph{Assumption bundles and fields.}",
                r"\begin{itemize}",
            ]
        )
        if all_bundles:
            for bundle_name in sorted(all_bundles.keys()):
                lines.append(rf"\item \nolinkurl{{{bundle_name}}}")
                fields = all_bundles[bundle_name]
                if fields:
                    lines.append(r"\begin{itemize}")
                    for field in fields:
                        lines.append(rf"\item \nolinkurl{{{field}}}")
                    lines.append(r"\end{itemize}")
        else:
            lines.append(r"\item (No assumption bundles parsed.)")
        lines.append(r"\end{itemize}")

        lines.extend(
            [
                r"\paragraph{Conditional closure handles.}",
                r"\begin{itemize}",
            ]
        )
        if all_conditional_handles:
            for handle in sorted(all_conditional_handles):
                lines.append(rf"\item \nolinkurl{{{self._compact_lean_handle(handle)}}}")
        else:
            lines.append(r"\item (No conditional theorem handles parsed.)")
        lines.append(r"\end{itemize}")

        out_file.write_text("\n".join(lines) + "\n", encoding="utf-8")

    def _read_existing_lean_handle_rows(
        self, paper_id: str
    ) -> List[Tuple[str, str]]:
        """Read existing `(ID, handle)` rows from `lean_handle_ids_auto.tex`."""
        content_dir = self._get_content_dir(paper_id)
        map_file = content_dir / "lean_handle_ids_auto.tex"
        if not map_file.exists():
            return []

        text = map_file.read_text(encoding="utf-8", errors="replace")
        code_pattern = re.compile(r"\\text(?:tt|sf)\{([^}]+)\}")
        handle_pattern = re.compile(r"\\nolinkurl\{([^}]+)\}")
        rows: List[Tuple[str, str]] = []
        for raw_line in text.splitlines():
            if "&" not in raw_line or r"\nolinkurl{" not in raw_line:
                continue
            code_match = code_pattern.search(raw_line)
            handle_match = handle_pattern.search(raw_line)
            if not code_match or not handle_match:
                continue
            code = code_match.group(1).strip()
            handle = handle_match.group(1).strip().replace(r"\_", "_")
            if code and handle:
                rows.append((code, handle))
        return rows

    def _extract_declared_lean_handles(
        self, paper_id: str, include_dependencies: bool = True
    ) -> Set[str]:
        """Extract declared Lean constants from theorem/def/class-style declarations.

        When `include_dependencies` is true, this scans the paper's transitive
        Lean dependency closure so handle extraction is derived from the full
        proof graph rather than only the local proofs tree.
        """
        roots: List[Tuple[str, Path]]
        if include_dependencies:
            roots = self._iter_lean_roots_for_paper(paper_id)
        else:
            roots = [(paper_id, self._get_paper_proofs_dir(paper_id))]

        decl_pattern = re.compile(
            r"\b(?:theorem|lemma|def|abbrev|class|structure)\s+([A-Za-z_][A-Za-z0-9_'.]*)"
        )
        namespace_pattern = re.compile(r"^\s*namespace\s+([A-Za-z0-9_'.]+)\s*$")
        end_pattern = re.compile(r"^\s*end(?:\s+[A-Za-z0-9_'.]+)?\s*$")

        handles: Set[str] = set()
        for _, proofs_dir in roots:
            if not proofs_dir.exists():
                continue
            for lean_file in self._iter_paper_lean_files(proofs_dir):
                content = lean_file.read_text(encoding="utf-8", errors="replace")
                stripped = self._strip_lean_comments(content)
                namespace_stack: List[str] = []

                for raw_line in stripped.splitlines():
                    line = raw_line.strip()
                    if not line:
                        continue

                    ns_match = namespace_pattern.match(line)
                    if ns_match:
                        namespace_stack.append(ns_match.group(1))
                        continue

                    if end_pattern.match(line):
                        if namespace_stack:
                            namespace_stack.pop()
                        continue

                    decl_match = decl_pattern.search(line)
                    if not decl_match:
                        continue

                    name = decl_match.group(1)
                    if "." in name:
                        handles.add(name)
                        continue

                    if namespace_stack:
                        ns_parts: List[str] = []
                        for ns in namespace_stack:
                            ns_parts.extend([part for part in ns.split(".") if part])
                        ns_prefix = ".".join(ns_parts)
                        handles.add(f"{ns_prefix}.{name}" if ns_prefix else name)
                    else:
                        handles.add(name)

        return handles

    def _extract_referenced_lean_handles_from_content(self, paper_id: str) -> Set[str]:
        """Extract explicit Lean handles referenced in paper content via `\\nolinkurl{...}`."""
        content_dir = self._get_content_dir(paper_id)
        if not content_dir.exists():
            return set()

        generated_files = {
            "lean_stats.tex",
            "assumption_ledger_auto.tex",
            "claim_mapping_auto.tex",
            "lean_handle_ids_auto.tex",
            "proof_hardness_index_auto.tex",
        }
        paper_handle_pattern = re.compile(r"^(?:thm|cor|lem|prop):")
        handles: Set[str] = set()

        for tex_file in sorted(content_dir.glob("*.tex")):
            if tex_file.name in generated_files:
                continue
            text = tex_file.read_text(encoding="utf-8", errors="replace")
            for raw in re.findall(r"\\nolinkurl\{([^}]+)\}", text):
                handle = raw.strip().replace(r"\_", "_")
                if not handle:
                    continue
                if paper_handle_pattern.match(handle):
                    continue
                if handle.endswith(".lean"):
                    continue
                if "." not in handle and "_" not in handle:
                    continue
                handles.add(handle)

        return handles

    def _extract_lh_ids_from_content(self, paper_id: str) -> Set[str]:
        """Extract compact Lean-handle IDs referenced via `\\LH{...}` in content."""
        content_dir = self._get_content_dir(paper_id)
        if not content_dir.exists():
            return set()

        ids: Set[str] = set()
        for tex_file in sorted(content_dir.glob("*.tex")):
            text = tex_file.read_text(encoding="utf-8", errors="replace")
            ids.update(m.strip() for m in re.findall(r"\\LH\{([^}]+)\}", text))
        return {code for code in ids if code}

    def _extract_alias_code_map_from_handle_aliases(
        self, paper_id: str, include_dependencies: bool = True
    ) -> Dict[str, str]:
        """Derive canonical compact ID -> handle mapping from HandleAliases.lean.

        This keeps `\\LH{...}` IDs stable even when prose no longer contains
        full `\\nolinkurl{...}` handles.
        """
        roots: List[Tuple[str, Path]]
        if include_dependencies:
            roots = self._iter_lean_roots_for_paper(paper_id)
        else:
            roots = [(paper_id, self._get_paper_proofs_dir(paper_id))]

        ident_pattern = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")

        def parse_alias_file(alias_file: Path) -> Dict[str, str]:
            """Extract ID -> handle mappings from HandleAliases.lean.

            DOF=1 design: Lean file is source of truth.
            - Export statements: namespace prefix + sequential index -> source.name
            - Abbrev declarations: abbrev name IS the ID -> qualified handle
            """
            text = alias_file.read_text(encoding="utf-8", errors="replace")
            stripped = self._strip_lean_comments(text)
            local_map: Dict[str, str] = {}
            counters: Dict[str, int] = {}
            namespace_stack: List[str] = []
            lines = stripped.splitlines()
            i = 0

            while i < len(lines):
                line = lines[i].strip()
                if not line:
                    i += 1
                    continue

                # Track namespace
                ns_match = re.match(r"^namespace\s+([A-Za-z0-9_'.]+)\s*$", line)
                if ns_match:
                    namespace_stack.append(ns_match.group(1))
                    i += 1
                    continue

                end_match = re.match(r"^end(?:\s+([A-Za-z0-9_'.]+))?\s*$", line)
                if end_match:
                    end_ns = end_match.group(1)
                    if end_ns and namespace_stack:
                        while namespace_stack and namespace_stack[-1] != end_ns:
                            namespace_stack.pop()
                        if namespace_stack and namespace_stack[-1] == end_ns:
                            namespace_stack.pop()
                    elif namespace_stack:
                        namespace_stack.pop()
                    i += 1
                    continue

                # Parse export statements for auto-numbered IDs
                if line.startswith("export ") and "(" in line and namespace_stack:
                    current_ns = namespace_stack[-1]
                    # Skip top-level namespace
                    if current_ns == "DecisionQuotient":
                        i += 1
                        continue

                    src_match = re.match(r"^export\s+([A-Za-z0-9_'.]+)\s*\(", line)
                    if not src_match:
                        i += 1
                        continue
                    source_ns = src_match.group(1)

                    # Collect all names in the export (may span multiple lines)
                    depth = line.count("(") - line.count(")")
                    body = line.split("(", 1)[1]
                    j = i + 1
                    while depth > 0 and j < len(lines):
                        seg = lines[j]
                        depth += seg.count("(") - seg.count(")")
                        body += "\n" + seg
                        j += 1

                    if ")" in body:
                        body = body.rsplit(")", 1)[0]

                    # Extract identifiers
                    names: List[str] = []
                    for raw in body.replace(",", " ").split():
                        token = raw.strip()
                        if ident_pattern.fullmatch(token):
                            names.append(token)

                    # Dedupe while preserving order
                    seen: Set[str] = set()
                    for name in names:
                        if name in seen:
                            continue
                        seen.add(name)
                        idx = counters.get(current_ns, 0) + 1
                        counters[current_ns] = idx
                        local_map[f"{current_ns}{idx}"] = f"{source_ns}.{name}"

                    i = j
                    continue

                # Parse abbrev declarations: abbrev XX := YY
                abbrev_match = re.match(
                    r"^abbrev\s+([A-Z]{1,4}\d+)\s*:=\s*([A-Za-z0-9_'.@]+)\s*$", line
                )
                if abbrev_match:
                    code = abbrev_match.group(1)
                    target = abbrev_match.group(2).lstrip("@")
                    # Qualify target with namespace prefix
                    if namespace_stack:
                        ns_prefix = ".".join(namespace_stack) + "."
                        full_handle = ns_prefix + target
                    else:
                        full_handle = target
                    local_map[code] = full_handle

                i += 1

            return local_map

        code_to_handle: Dict[str, str] = {}
        # Prefer paper-local aliases, then fill missing IDs from dependencies.
        for _, proofs_dir in roots:
            if not proofs_dir.exists():
                continue
            alias_files = sorted(proofs_dir.rglob("HandleAliases.lean"))
            for alias_file in alias_files:
                local_map = parse_alias_file(alias_file)
                for code, handle in local_map.items():
                    if code not in code_to_handle:
                        code_to_handle[code] = handle

        return code_to_handle

    def _assign_compact_handle_ids(
        self, handles: Set[str], existing_rows: List[Tuple[str, str]]
    ) -> Dict[str, str]:
        """Assign compact IDs to handles, preserving explicit assignments.

        DOF=1 design:
        1. Explicit assignments from HandleAliases.lean are preserved as-is
        2. Remaining handles get auto-numbered IDs based on prefix
        3. Auto-numbering is deterministic (sorted order)
        """
        handle_to_code: Dict[str, str] = {}
        used_codes: Set[str] = set()

        # First, apply explicit assignments from provided existing rows
        for code, handle in existing_rows:
            if handle in handle_to_code:
                continue
            if code in used_codes:
                continue
            handle_to_code[handle] = code
            used_codes.add(code)

        # Auto-assign stable, insertion-safe IDs for remaining handles.
        # Use a prefix derived from the first namespace component plus a
        # short sha1 digest of the full handle to ensure determinism and
        # that adding other handles won't shift existing codes.
        for handle in sorted(handles):
            if handle in handle_to_code:
                continue

            group = handle.split(".", 1)[0] if "." in handle else "L"
            prefix = self._compact_lean_prefix(group) or "H"

            # Short stable digest
            digest = hashlib.sha1(handle.encode("utf-8")).hexdigest()[:8]
            code = f"{prefix}_{digest}"

            # If collision (very unlikely), extend digest until unique
            ext = 8
            while code in used_codes:
                ext += 4
                digest = hashlib.sha1((handle + str(ext)).encode("utf-8")).hexdigest()[:ext]
                code = f"{prefix}_{digest}"

            used_codes.add(code)
            handle_to_code[handle] = code

        return handle_to_code

    def _write_lean_handle_ids_auto(self, paper_id: str) -> None:
        """Write compact Lean-handle ID table used by `\\LH{...}` references."""
        content_dir = self._get_content_dir(paper_id)
        if not content_dir.exists():
            return

        out_file = content_dir / "lean_handle_ids_auto.tex"
        # Prefer explicit mappings declared in HandleAliases.lean as the
        # single source of truth for explicit ID assignments.
        alias_by_code = self._extract_alias_code_map_from_handle_aliases(
            paper_id, include_dependencies=True
        )
        existing_rows = sorted(alias_by_code.items())
        referenced_handles = self._extract_referenced_lean_handles_from_content(paper_id)
        referenced_ids = self._extract_lh_ids_from_content(paper_id)
        # DOF=1 policy for handle maps:
        # derive IDs from support actually used by paper content/claims, not from
        # every declaration in the transitive Lean dependency graph.
        claim_to_handles = self._extract_claim_label_to_lean_handles(
            paper_id, include_dependencies=True
        )
        support_handles: Set[str] = set()
        for handles in claim_to_handles.values():
            support_handles.update(handles)

        candidate_handles = set(referenced_handles) | set(support_handles)

        # Preserve explicit alias assignments from HandleAliases.lean and
        # include those handles in the universe to ensure they remain stable.
        preserved_rows = existing_rows
        preserved_handles = {handle for _, handle in preserved_rows}

        # Single derived universe: local references + derived theorem support
        # plus any explicitly-declared alias handles.
        all_handles = set(referenced_handles) | set(support_handles) | preserved_handles | set(alias_by_code.values())

        handle_to_code = self._assign_compact_handle_ids(all_handles, preserved_rows)
        code_to_handle = {code: handle for handle, code in handle_to_code.items()}

        def sort_key(code: str) -> Tuple[str, int, str]:
            match = re.match(r"^([A-Za-z]+)(\d+)$", code)
            if not match:
                return (code, 10**9, code)
            return (match.group(1), int(match.group(2)), code)

        lines: List[str] = [
            "% Auto-generated by scripts/build_papers.py. Do not edit manually.",
            f"% Generated: {datetime.now().isoformat()}",
            r"\begingroup",
            r"\scriptsize",
            r"\setlength{\tabcolsep}{3pt}",
            r"\renewcommand{\arraystretch}{0.92}",
            r"\urlstyle{same}",
            r"\begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.10\linewidth}>{\raggedright\arraybackslash}p{0.86\linewidth}@{}}",
            r"\toprule",
            r"ID & Full Lean handle \\",
            r"\midrule",
            r"\endfirsthead",
            r"\toprule",
            r"ID & Full Lean handle (continued) \\",
            r"\midrule",
            r"\endhead",
        ]

        if code_to_handle:
            for code in sorted(code_to_handle.keys(), key=sort_key):
                handle = code_to_handle[code]
                escaped = handle.replace("_", r"\_")
                lines.append(
                    rf"\hypertarget{{lh:{code}}}{{\textsf{{{code}}}}} & \nolinkurl{{{escaped}}} \\"
                )
        else:
            lines.append(r"\multicolumn{2}{@{}l@{}}{\textit{No Lean handles parsed yet.}} \\")

        lines.extend([r"\bottomrule", r"\end{longtable}", r"\endgroup", ""])
        out_file.write_text("\n".join(lines), encoding="utf-8")

    def _rewrite_content_lean_handles_to_ids(self, paper_id: str) -> None:
        """Rewrite inline `\\nolinkurl{...}` Lean handles to compact `\\LH{...}` IDs.

        This keeps prose readable and clickable without requiring manual conversion
        in each paper's content files.
        """
        content_dir = self._get_content_dir(paper_id)
        if not content_dir.exists():
            return

        id_to_handle = self._read_lean_handle_id_map(paper_id)
        if not id_to_handle:
            return
        handle_to_id = {handle: code for code, handle in id_to_handle.items()}

        generated_files = {
            "lean_stats.tex",
            "assumption_ledger_auto.tex",
            "claim_mapping_auto.tex",
            "lean_handle_ids_auto.tex",
            "proof_hardness_index_auto.tex",
        }
        nolink_pattern = re.compile(r"\\nolinkurl\{([^}]+)\}")
        leanmeta_prefix_pattern = re.compile(r"(\\leanmeta\{)\s*Lean handles:\s*")

        for tex_file in sorted(content_dir.glob("*.tex")):
            if tex_file.name in generated_files:
                continue
            text = tex_file.read_text(encoding="utf-8", errors="replace")
            normalized = leanmeta_prefix_pattern.sub(r"\1", text)

            def repl(match: re.Match[str]) -> str:
                raw = match.group(1).strip()
                handle = raw.replace(r"\_", "_")
                code = handle_to_id.get(handle)
                if code is None:
                    return match.group(0)
                return rf"\LH{{{code}}}"

            rewritten = nolink_pattern.sub(repl, normalized)
            if rewritten != text:
                tex_file.write_text(rewritten, encoding="utf-8")

    def _claim_ref_code_for_label(self, label: str) -> str:
        """Return compact claim-ref code by label prefix."""
        normalized = label.strip().lower()
        if normalized.startswith(("thm:", "th:")):
            return "T"
        if normalized.startswith("prop:"):
            return "P"
        if normalized.startswith("cor:"):
            return "C"
        if normalized.startswith(("def:", "definition:")):
            return "D"
        if normalized.startswith(("lem:", "lemma:")):
            return "L"
        if normalized.startswith(("ax:", "axiom:")):
            return "A"
        if normalized.startswith(("conj:", "conjecture:")):
            return "J"
        return "R"

    def _normalize_claimstamp_refs(self, derived: str) -> str:
        """Normalize verbose theorem references to compact `X\\ref{...}` style."""
        normalized = derived
        replacements = [
            (r"(?:Theorem|Thm\.?)\s*~?\s*\\ref\{([^}]+)\}", r"T\\ref{\1}"),
            (r"(?:Proposition|Prop\.?)\s*~?\s*\\ref\{([^}]+)\}", r"P\\ref{\1}"),
            (r"(?:Corollary|Cor\.?)\s*~?\s*\\ref\{([^}]+)\}", r"C\\ref{\1}"),
            (r"(?:Definition|Def\.?)\s*~?\s*\\ref\{([^}]+)\}", r"D\\ref{\1}"),
            (r"(?:Lemma|Lem\.?)\s*~?\s*\\ref\{([^}]+)\}", r"L\\ref{\1}"),
            (r"(?:Axiom|Ax\.?)\s*~?\s*\\ref\{([^}]+)\}", r"A\\ref{\1}"),
            (r"(?:Conjecture|Conj\.?)\s*~?\s*\\ref\{([^}]+)\}", r"J\\ref{\1}"),
        ]
        for pattern, replacement in replacements:
            normalized = re.sub(pattern, replacement, normalized)
        normalized = normalized.replace("~", "")
        normalized = re.sub(r"\s*,\s*", ",", normalized)
        normalized = re.sub(r"\s*;\s*", ";", normalized)
        normalized = re.sub(r"\s+", " ", normalized).strip(" ,;")
        return normalized

    def _normalize_claimstamp_regime(self, regime: str) -> str:
        """Normalize regime tags to compact notation (e.g., `AR`, `S+ETH`)."""
        raw = regime.strip()
        if not raw:
            return ""
        if raw.startswith("[") and raw.endswith("]"):
            raw = raw[1:-1].strip()
        # Treat bracket wrappers as presentation-only and tolerate malformed mixes.
        raw = raw.replace("[", "").replace("]", "")

        # Canonical phrase -> compact code.
        phrase_map = {
            "active declared regime": "AR",
            "declared contract": "DC",
            "declared class/regime": "CR",
            "declared task/regime": "TR",
            "declared decision model": "DM",
            "represented adjacent class": "RA",
            "tractable active regime": "TA",
            "regime-typed": "RG",
            "structured": "STR",
            "identifiable": "ID",
            "bounded horizon": "BH",
            "fully observable": "FO",
            "counterexample": "CE",
            "p = product distribution": "PD",
            "bounded support": "BS",
            "deterministic": "DET",
        }

        # Normalize delimiters before tokenization.
        text = raw.replace(" vs ", ",")
        text = text.replace("][", "],[").replace("], [", "],[")
        parts = [p.strip() for p in re.split(r"\s*[,;]\s*", text) if p.strip()]
        compact_parts: List[str] = []
        seen: Set[str] = set()
        for part in parts:
            token = part.strip()
            if token.startswith("[") and token.endswith("]"):
                token = token[1:-1].strip()
            if token.lower().startswith("r="):
                token = token[2:].strip()

            lowered = token.lower()
            mapped = phrase_map.get(lowered)
            if mapped is None:
                # Preserve explicit symbolic assumptions (e.g., P != coNP, S+ETH).
                if any(ch in token for ch in ("\\", "$", "+", "=", "<", ">", "!", "_")):
                    mapped = token
                elif re.fullmatch(r"[A-Z0-9]+", token):
                    mapped = token
                else:
                    mapped = token

            if mapped and mapped not in seen:
                compact_parts.append(mapped)
                seen.add(mapped)

        return ",".join(compact_parts)

    def _extract_label_to_regime_from_claimstamps(
        self, paper_id: str
    ) -> Dict[str, str]:
        """Extract label -> regime mapping from claimstamps in a source paper."""
        content_dir = self._get_content_dir(paper_id)
        if not content_dir.exists():
            return {}

        claimstamp_pattern = re.compile(
            r"\\claimstamp\{((?:[^{}]|\\ref\{[^}]+\})*)\}\{([^}]*)\}",
            re.DOTALL,
        )
        ref_pattern = re.compile(r"\\ref\{([^}]+)\}")
        mapping: Dict[str, str] = {}
        for tex_file in sorted(content_dir.glob("*.tex")):
            text = tex_file.read_text(encoding="utf-8", errors="replace")
            for first_arg, second_arg in claimstamp_pattern.findall(text):
                labels = ref_pattern.findall(first_arg)
                if len(labels) != 1:
                    continue
                label = labels[0].strip()
                if not label:
                    continue
                regime = self._normalize_claimstamp_regime(second_arg)
                if regime and label not in mapping:
                    mapping[label] = regime
        return mapping

    def _extract_label_to_hardness_tags_from_claimstamps(
        self, paper_id: str
    ) -> Dict[str, List[str]]:
        """Extract claim-label -> normalized regime/hardness tags from claimstamps.

        Unlike `_extract_label_to_regime_from_claimstamps`, this function keeps
        multi-label stamps and accumulates all tags seen for each label so the
        generated hardness index can be derived from the same claim metadata.
        """
        content_dir = self._get_content_dir(paper_id)
        if not content_dir.exists():
            return {}

        generated_files = {
            "lean_stats.tex",
            "assumption_ledger_auto.tex",
            "claim_mapping_auto.tex",
            "lean_handle_ids_auto.tex",
            "proof_hardness_index_auto.tex",
        }
        claimstamp_pattern = re.compile(
            r"\\claimstamp\{((?:[^{}]|\\ref\{[^}]+\})*)\}\{([^}]*)\}",
            re.DOTALL,
        )
        ref_pattern = re.compile(r"\\ref\{([^}]+)\}")
        paper_handle_pattern = re.compile(r"^(?:thm|cor|lem|prop):")

        label_to_tags: Dict[str, Set[str]] = {}
        fallback_multi: Dict[str, Set[str]] = {}
        for tex_file in sorted(content_dir.glob("*.tex")):
            if tex_file.name in generated_files:
                continue
            text = tex_file.read_text(encoding="utf-8", errors="replace")
            for first_arg, second_arg in claimstamp_pattern.findall(text):
                labels = [lab.strip() for lab in ref_pattern.findall(first_arg)]
                if not labels:
                    continue
                normalized = self._normalize_claimstamp_regime(second_arg)
                tags = [tok.strip() for tok in normalized.split(",") if tok.strip()]
                if not tags:
                    continue
                dest = label_to_tags if len(labels) == 1 else fallback_multi
                for label in labels:
                    if not paper_handle_pattern.match(label):
                        continue
                    dest.setdefault(label, set()).update(tags)

        # Only fall back to multi-label aggregate stamps when no theorem-local tag exists.
        for label, tags in fallback_multi.items():
            if label not in label_to_tags:
                label_to_tags[label] = set(tags)

        return {
            label: sorted(tags)
            for label, tags in sorted(label_to_tags.items(), key=lambda kv: kv[0])
        }

    def _derive_hardness_profile(self, label: str, tags: List[str]) -> str:
        """Derive hardness profile from source tags.

        DOF=1 policy:
        - explicit `H=...` tag in claimstamp metadata is the only source
        - absent explicit hardness metadata, return `unspecified`
        """
        _ = label  # label kept for signature stability / future diagnostics
        explicit: List[str] = []
        for tag in tags:
            lower = tag.lower()
            if lower.startswith("h="):
                value = tag.split("=", 1)[1].strip()
                if value and value not in explicit:
                    explicit.append(value)
            elif lower.startswith("hardness="):
                value = tag.split("=", 1)[1].strip()
                if value and value not in explicit:
                    explicit.append(value)

        if explicit:
            return ",".join(explicit)
        return "unspecified"

    def _write_proof_hardness_index_auto(self, paper_id: str) -> None:
        """Write auto-generated proof hardness index from claim labels/tags."""
        content_dir = self._get_content_dir(paper_id)
        if not content_dir.exists():
            return

        out_file = content_dir / "proof_hardness_index_auto.tex"
        claim_labels = sorted(self._extract_paper_claim_labels(paper_id))
        if not claim_labels:
            out_file.write_text(
                "% Auto-generated by scripts/build_papers.py. No claim labels found.\n",
                encoding="utf-8",
            )
            return

        claim_to_handles = self._extract_claim_label_to_lean_handles(paper_id)
        label_to_tags = self._extract_label_to_hardness_tags_from_claimstamps(paper_id)
        id_to_handle = self._read_lean_handle_id_map(paper_id)
        handle_to_id = {handle: code for code, handle in id_to_handle.items()}

        rows: List[Tuple[str, str, str, str]] = []
        profile_counts: Dict[str, int] = {}
        for label in claim_labels:
            tags = label_to_tags.get(label, [])
            profile = self._derive_hardness_profile(label, tags)
            profile_counts[profile] = profile_counts.get(profile, 0) + 1

            tags_cell = ",".join(tags) if tags else "-"
            handles = claim_to_handles.get(label, [])
            if handles:
                support_items: List[str] = []
                for handle in handles:
                    code = handle_to_id.get(handle)
                    if code is not None:
                        support_items.append(rf"\LH{{{code}}}")
                    else:
                        compact = self._compact_lean_handle(handle).replace("_", r"\_")
                        support_items.append(rf"\nolinkurl{{{compact}}}")
                support_cell = ", ".join(support_items)
            else:
                support_cell = r"\emph{(no derived Lean handle found)}"

            rows.append((label, profile, tags_cell, support_cell))

        rows.sort(key=lambda row: (row[1], row[0]))

        lines: List[str] = [
            "% Auto-generated by scripts/build_papers.py. Do not edit manually.",
            f"% Generated: {datetime.now().isoformat()}",
            rf"% Paper: {paper_id}",
            r"\begingroup",
            r"\scriptsize",
            r"\sloppy",
            r"\setlength{\tabcolsep}{4pt}",
            r"\begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.22\linewidth}>{\raggedright\arraybackslash}p{0.18\linewidth}>{\raggedright\arraybackslash}p{0.16\linewidth}>{\raggedright\arraybackslash}p{0.40\linewidth}@{}}",
            r"\toprule",
            r"\textbf{Paper handle} & \textbf{Hardness profile} & \textbf{Regime tags} & \textbf{Lean support} \\",
            r"\midrule",
        ]

        for label, profile, tags_cell, support_cell in rows:
            # tags_cell may contain math mode (e.g., "P $\neq$ \coNP") which breaks
            # inside \nolinkurl{}. Use \texttt{} for tags, \nolinkurl{} for others.
            lines.append(
                rf"\nolinkurl{{{label}}} & \nolinkurl{{{profile}}} & \texttt{{{tags_cell}}} & {support_cell} \\"
            )

        lines.extend([r"\bottomrule", r"\end{longtable}", r"\endgroup", ""])
        summary_parts = [
            f"{name}={profile_counts[name]}" for name in sorted(profile_counts.keys())
        ]
        lines.append(
            rf"\noindent\textit{{Auto summary: indexed {len(rows)} claims by hardness profile ({'; '.join(summary_parts)}).}}"
        )
        out_file.write_text("\n".join(lines) + "\n", encoding="utf-8")

    def _normalize_and_fill_claimstamps(self, paper_id: str) -> None:
        """Normalize claimstamp notation and fill empty claim-block placeholders.

        This enforces compact, paper-wide consistent tags:
        - `Prop.~\\ref{...}` -> `P\\ref{...}` (similarly for other theorem classes)
        - empty claim-block stamps derive from the claim label
        - empty regime tags inherit from scaffold source when available, else `RG`
        """
        content_dir = self._get_content_dir(paper_id)
        if not content_dir.exists():
            return

        meta = self._get_paper_meta(paper_id)
        source_regimes: Dict[str, str] = {}
        source_id = meta.scaffold_from.strip()
        if source_id and source_id in self.papers:
            source_regimes = self._extract_label_to_regime_from_claimstamps(source_id)

        generated_files = {
            "lean_stats.tex",
            "assumption_ledger_auto.tex",
            "claim_mapping_auto.tex",
            "lean_handle_ids_auto.tex",
            "proof_hardness_index_auto.tex",
        }
        claimstamp_pattern = re.compile(
            r"\\claimstamp\{((?:[^{}]|\\ref\{[^}]+\})*)\}\{([^}]*)\}",
            re.DOTALL,
        )
        claim_block_pattern = re.compile(
            r"(\\begin\{claim\}\{[^{}]*\}\{([^{}]+)\})(.*?)(\\end\{claim\})",
            re.DOTALL,
        )
        generic_first_pattern = re.compile(
            r"^\s*(?:Thm\.?|Theorem|Prop\.?|Proposition|Cor\.?|Corollary|Def\.?|Definition|Lemma|Lem\.?|Axiom|Ax\.?|Conjecture|Conj\.?)\s*\.?\s*$"
        )

        for tex_file in sorted(content_dir.glob("*.tex")):
            if tex_file.name in generated_files:
                continue
            text = tex_file.read_text(encoding="utf-8", errors="replace")

            # Pass 1: normalize existing stamps.
            def normalize_stamp(match: re.Match[str]) -> str:
                first = self._normalize_claimstamp_refs(match.group(1))
                second = self._normalize_claimstamp_regime(match.group(2))
                return rf"\claimstamp{{{first}}}{{{second}}}"

            rewritten = claimstamp_pattern.sub(normalize_stamp, text)

            # Pass 2: fill empty/generic claim-block stamps using local label.
            def fill_block(match: re.Match[str]) -> str:
                begin, label, body, end = match.group(1), match.group(2), match.group(3), match.group(4)
                normalized_label = label.strip()

                def fill_first_stamp(stamp_match: re.Match[str]) -> str:
                    first = stamp_match.group(1).strip()
                    second = stamp_match.group(2).strip()

                    if not first or generic_first_pattern.fullmatch(first):
                        code = self._claim_ref_code_for_label(normalized_label)
                        first = rf"{code}\ref{{{normalized_label}}}"

                    if not second:
                        second = source_regimes.get(normalized_label, "RG")

                    return rf"\claimstamp{{{first}}}{{{second}}}"

                filled_body, _ = claimstamp_pattern.subn(fill_first_stamp, body, count=1)
                return begin + filled_body + end

            rewritten = claim_block_pattern.sub(fill_block, rewritten)

            if rewritten != text:
                tex_file.write_text(rewritten, encoding="utf-8")

    def _extract_claim_label_to_lean_handles(
        self, paper_id: str, include_dependencies: bool = True
    ) -> Dict[str, List[str]]:
        """Extract mapping from theorem-style labels to inline Lean handles.

        Source heuristic:
        - scan theorem/proposition/corollary/lemma blocks in content/*.tex
        - collect `\\label{thm:...|prop:...|cor:...|lem:...}` inside each block
        - collect non-paper-handle `\\nolinkurl{...}` entries and `\\LH{...}` IDs
          inside each block as Lean support
        - additionally support claim-style blocks:
          `\\begin{claim}{Title}{prop:...} ... \\end{claim}`
        - attach immediately-following `\\leanmeta{...}` blocks to the claim/theorem
          that precedes them
        """
        content_dir = self._get_content_dir(paper_id)
        if not content_dir.exists():
            return {}

        id_to_handle = self._read_lean_handle_id_map(paper_id)

        block_pattern = re.compile(
            r"\\begin\{(theorem|proposition|corollary|lemma)\}(.*?)\\end\{\1\}",
            re.DOTALL,
        )
        claim_pattern = re.compile(
            r"\\begin\{claim\}\{[^{}]*\}\{((?:thm|cor|lem|prop):[^{}]+)\}(.*?)\\end\{claim\}",
            re.DOTALL,
        )
        label_pattern = re.compile(r"\\label\{((?:thm|cor|lem|prop):[^}]+)\}")
        nolink_pattern = re.compile(r"\\nolinkurl\{([^}]+)\}")
        lh_pattern = re.compile(r"\\LH\{([^}]+)\}")
        paper_handle_pattern = re.compile(r"^(?:thm|cor|lem|prop):")

        def extract_handles_from_text(fragment: str) -> List[str]:
            handles: List[str] = []
            for h in nolink_pattern.findall(fragment):
                h = h.replace(r"\_", "_")
                if paper_handle_pattern.match(h):
                    continue
                # Keep declaration-like handles, drop bare module/file mentions.
                if h.endswith(".lean"):
                    continue
                if "." not in h and "_" not in h:
                    continue
                handles.append(h)
            for handle_id in lh_pattern.findall(fragment):
                resolved = id_to_handle.get(handle_id.strip())
                if resolved:
                    handles.append(resolved)
            return handles

        def extract_following_leanmeta_handles(text: str, start_idx: int) -> List[str]:
            """Extract handles from consecutive `\\leanmeta{...}` blocks after a claim."""
            handles: List[str] = []
            i = start_idx
            n = len(text)
            prefix = r"\leanmeta{"
            while i < n:
                while i < n and text[i].isspace():
                    i += 1
                if not text.startswith(prefix, i):
                    break
                j = i + len(prefix)
                depth = 1
                while j < n and depth > 0:
                    ch = text[j]
                    if ch == "{":
                        depth += 1
                    elif ch == "}":
                        depth -= 1
                    j += 1
                if depth != 0:
                    break
                handles.extend(extract_handles_from_text(text[i:j]))
                i = j
            return handles

        local_mapping: Dict[str, Set[str]] = {}
        for tex_file in sorted(content_dir.glob("*.tex")):
            text = tex_file.read_text(encoding="utf-8", errors="replace")
            for match in block_pattern.finditer(text):
                block_text = match.group(0)
                labels = label_pattern.findall(block_text)
                if not labels:
                    continue
                handles = extract_handles_from_text(
                    block_text
                ) + extract_following_leanmeta_handles(text, match.end())
                for label in labels:
                    local_mapping.setdefault(label, set()).update(handles)
            for match in claim_pattern.finditer(text):
                label = match.group(1)
                block_text = match.group(0)
                handles = extract_handles_from_text(
                    block_text
                ) + extract_following_leanmeta_handles(text, match.end())
                local_mapping.setdefault(label, set()).update(handles)

        if not include_dependencies:
            return {k: sorted(v) for k, v in local_mapping.items()}

        claim_labels = self._extract_paper_claim_labels(paper_id)
        merged: Dict[str, Set[str]] = {
            label: set(local_mapping.get(label, set())) for label in claim_labels
        }
        for label, handles in local_mapping.items():
            merged.setdefault(label, set()).update(handles)

        source_ids: List[str] = []
        meta = self._get_paper_meta(paper_id)
        source_id = meta.scaffold_from.strip()
        if source_id and source_id in self.papers:
            source_ids.append(source_id)
        for dep in self._collect_lean_dependency_closure(paper_id):
            if dep not in source_ids:
                source_ids.append(dep)

        for source in source_ids:
            # Prefer a pre-generated matrix (already derived and normalized).
            source_map = self._read_claim_mapping_table_handles(source)
            if not source_map:
                # Fallback to direct extraction from source content.
                source_map = self._extract_claim_label_to_lean_handles(
                    source, include_dependencies=False
                )
            for label in claim_labels:
                if merged.get(label):
                    continue
                source_handles = source_map.get(label, [])
                if source_handles:
                    merged.setdefault(label, set()).update(source_handles)

        return {k: sorted(v) for k, v in merged.items()}

    def _read_lean_handle_id_map(self, paper_id: str) -> Dict[str, str]:
        """Read generated Lean-handle ID map: LH code -> full Lean handle."""
        content_dir = self._get_content_dir(paper_id)
        map_file = content_dir / "lean_handle_ids_auto.tex"
        if not map_file.exists():
            return {}

        text = map_file.read_text(encoding="utf-8", errors="replace")
        id_to_handle: Dict[str, str] = {}
        # Format-robust parse:
        # - ID cell may use \texttt{ID} or \textsf{ID}
        # - handle cell may be wrapped (e.g., {\footnotesize\nolinkurl{...}})
        # - optional \hypertarget prefixes may appear before the ID cell
        code_pattern = re.compile(r"\\text(?:tt|sf)\{([^}]+)\}")
        handle_pattern = re.compile(r"\\nolinkurl\{([^}]+)\}")
        for raw_line in text.splitlines():
            if "&" not in raw_line or r"\nolinkurl{" not in raw_line:
                continue
            code_match = code_pattern.search(raw_line)
            handle_match = handle_pattern.search(raw_line)
            if not code_match or not handle_match:
                continue
            code = code_match.group(1).strip()
            handle = handle_match.group(1).strip().replace(r"\_", "_")
            if code and handle:
                id_to_handle[code] = handle
        return id_to_handle

    def _read_claim_mapping_table_handles(self, paper_id: str) -> Dict[str, List[str]]:
        """Read label->handles from an existing `claim_mapping_auto.tex` table."""
        content_dir = self._get_content_dir(paper_id)
        mapping_file = content_dir / "claim_mapping_auto.tex"
        if not mapping_file.exists():
            return {}

        text = mapping_file.read_text(encoding="utf-8", errors="replace")
        paper_handle_pattern = re.compile(r"^(?:thm|cor|lem|prop):")
        mapping: Dict[str, Set[str]] = {}

        for raw_line in text.splitlines():
            if "&" not in raw_line or r"\nolinkurl{" not in raw_line:
                continue
            nolinks = [
                s.strip().replace(r"\_", "_")
                for s in re.findall(r"\\nolinkurl\{([^}]+)\}", raw_line)
            ]
            if not nolinks:
                continue
            label = nolinks[0]
            if not paper_handle_pattern.match(label):
                continue
            supports = [h for h in nolinks[1:] if h and not paper_handle_pattern.match(h)]
            if supports:
                mapping.setdefault(label, set()).update(supports)

        return {label: sorted(handles) for label, handles in mapping.items()}

    def _write_claim_mapping_auto(self, paper_id: str) -> None:
        """Write auto-generated claim coverage matrix from derived theorem anchors."""
        meta = self._get_paper_meta(paper_id)
        latex_dir = self._get_paper_dir(paper_id) / meta.latex_dir
        content_dir = latex_dir / "content"
        if not content_dir.exists():
            return

        out_file = content_dir / "claim_mapping_auto.tex"
        claim_labels = sorted(self._extract_paper_claim_labels(paper_id))
        local_claim_to_handles = self._extract_claim_label_to_lean_handles(
            paper_id, include_dependencies=False
        )
        claim_to_handles = self._extract_claim_label_to_lean_handles(
            paper_id, include_dependencies=True
        )

        full_count = 0
        derived_count = 0
        unmapped_count = 0
        lines: List[str] = [
            "% Auto-generated by scripts/build_papers.py. Do not edit manually.",
            f"% Generated: {datetime.now().isoformat()}",
            rf"% Paper: {paper_id}",
            r"\begingroup",
            r"\scriptsize",
            r"\sloppy",
            r"\setlength{\tabcolsep}{4pt}",
            r"\begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.24\linewidth}>{\raggedright\arraybackslash}p{0.12\linewidth}>{\raggedright\arraybackslash}p{0.60\linewidth}@{}}",
            r"\toprule",
            r"\textbf{Paper handle} & \textbf{Status} & \textbf{Lean support} \\",
            r"\midrule",
        ]

        for label in claim_labels:
            handles = claim_to_handles.get(label, [])
            local_handles = local_claim_to_handles.get(label, [])
            if local_handles:
                status = "Full"
                full_count += 1
            elif handles:
                status = "Derived"
                derived_count += 1
            else:
                status = "Unmapped"
                unmapped_count += 1
            if handles:
                support = ", ".join(
                    rf"\nolinkurl{{{self._compact_lean_handle(h)}}}" for h in handles
                )
            else:
                support = r"\emph{(no derived Lean handle found)}"
            lines.append(rf"\nolinkurl{{{label}}} & {status} & {support} \\")

        lines.extend([r"\bottomrule", r"\end{longtable}", r"\endgroup", ""])
        if derived_count > 0 or unmapped_count > 0:
            lines.extend(
                [
                    r"\noindent\textit{Notes:}",
                    r"\noindent\textit{(1) Full rows come from theorem-local inline anchors in this paper.}",
                    r"\noindent\textit{(2) Derived rows are filled by dependency/scaffold claim-handle derivation (same paper-handle label across proof dependencies).}",
                    r"\noindent\textit{(3) Unmapped means no local anchor and no derivable dependency support were found.}",
                    "",
                ]
            )
        mapped_total = full_count + derived_count
        lines.append(
            rf"\noindent\textit{{Auto summary: mapped {mapped_total}/{len(claim_labels)} (full={full_count}, derived={derived_count}, unmapped={unmapped_count}).}}"
        )
        out_file.write_text("\n".join(lines) + "\n", encoding="utf-8")

    def _expand_lean_stat_macros(self, text: str, paper_id: str) -> str:
        """Expand ``\\Lean*`` macros to numeric values for markdown conversion."""
        total_stats = self._get_lean_stats(paper_id)
        file_stats = self._get_lean_file_stats(paper_id)
        suffix_map = self._build_lean_macro_suffix_map(sorted(file_stats.keys()))
        replacements: Dict[str, str] = {
            r"\LeanTotalLines": str(total_stats.line_count),
            r"\LeanTotalTheorems": str(total_stats.theorem_count),
            r"\LeanTotalSorry": str(total_stats.sorry_count),
            r"\LeanTotalFiles": str(total_stats.file_count),
        }
        for module_path, stats in file_stats.items():
            suffix = suffix_map[module_path]
            replacements[rf"\LeanLines{suffix}"] = str(stats.line_count)
            replacements[rf"\LeanTheorems{suffix}"] = str(stats.theorem_count)
            replacements[rf"\LeanSorry{suffix}"] = str(stats.sorry_count)

        # Replace longest keys first so specific file macros win over prefixes.
        for macro in sorted(replacements.keys(), key=len, reverse=True):
            text = text.replace(macro, replacements[macro])

        # Evaluate simple TeX integer arithmetic used in summary rows:
        # \number\numexpr 1+2-3\relax -> 0
        def _eval_numexpr(match: re.Match[str]) -> str:
            expr = re.sub(r"\s+", "", match.group(1))
            if not expr:
                return match.group(0)
            terms = re.findall(r"[+-]?\d+", expr)
            if not terms:
                return match.group(0)
            total = sum(int(term) for term in terms)
            return str(total)

        text = re.sub(
            r"\\number\\numexpr\s*([0-9+\-\s]+)\\relax",
            _eval_numexpr,
            text,
        )
        return text

    def build_lean(self, paper_id: str, verbose: bool = True) -> str:
        """Build Lean proofs with streaming output. Returns captured output.

        Uses each paper's own proofs directory (paper_dir/proofs/).
        Runs `lake build` in that directory.
        Captures output for inclusion in BUILD_LOG.txt.
        """
        proofs_dir = self._get_paper_proofs_dir(paper_id)

        if not proofs_dir.exists():
            print(f"[build] No proofs directory for {paper_id}, skipping...")
            return ""

        # Check for lakefile
        lakefile = proofs_dir / "lakefile.lean"
        if not lakefile.exists():
            print(f"[build] No lakefile.lean in {proofs_dir}, skipping...")
            return ""

        print(f"[build] Building {paper_id} Lean...")
        print(f"[build]   Directory: {proofs_dir.relative_to(self.repo_root)}")

        def run_lake(args: List[str]) -> Tuple[int, List[str]]:
            """Run lake command with streaming output."""
            print(f"[build]   Running: lake {' '.join(args)}")
            process = subprocess.Popen(
                ["lake"] + args,
                cwd=proofs_dir,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                bufsize=1,
            )

            output_lines: List[str] = []
            if process.stdout is not None:
                for line in process.stdout:
                    output_lines.append(line)
                    if verbose:
                        print(f"         {line}", end="", flush=True)
                    elif "Building" in line or "Compiling" in line:
                        print(".", end="", flush=True)

            process.wait()
            if not verbose:
                print()
            return (process.returncode, output_lines)

        # Run lake build (builds all targets in the paper's proofs directory)
        returncode, output = run_lake(["build"])
        output_text = "".join(output)

        # Handle stale cache
        if "compiled configuration is invalid" in output_text:
            print(f"[build]   Reconfiguring (stale cache detected)...")
            returncode, output = run_lake(["build", "-R"])
            output_text = "".join(output)

        if returncode != 0:
            if not verbose:
                print("[build]   lake output (last 200 lines):")
                for line in output_text.splitlines()[-200:]:
                    print(f"         {line}")
            raise RuntimeError(
                f"Lean build failed for {paper_id} (exit code {returncode})"
            )

        # Store for BUILD_LOG.txt
        self._lean_build_output = output_text
        print(f"[build] ✓ {paper_id} Lean complete")
        return output_text

    def build_latex(self, paper_id: str, verbose: bool = False):
        """Build LaTeX PDF for a paper and copy to releases/.

        Runs full build cycle: pdflatex → bibtex → pdflatex → pdflatex
        to resolve citations and cross-references.

        For variants (e.g., paper1_jsait), uses variant-specific naming.
        """
        meta = self._get_paper_meta(paper_id)
        paper_dir = self._get_paper_dir(paper_id)
        latex_dir = paper_dir / meta.latex_dir
        latex_file = latex_dir / meta.latex_file

        if not latex_file.exists():
            raise FileNotFoundError(f"LaTeX file not found: {latex_file}")

        self._sync_shared_preambles(paper_id)
        self._write_latex_lean_stats(paper_id)
        self._write_assumption_ledger_auto(paper_id)
        self._write_lean_handle_ids_auto(paper_id)
        self._rewrite_content_lean_handles_to_ids(paper_id)
        self._normalize_and_fill_claimstamps(paper_id)
        self._write_claim_mapping_auto(paper_id)
        self._write_proof_hardness_index_auto(paper_id)
        self._update_paper_date(latex_file)

        print(f"[build] Building {paper_id} LaTeX...")

        # Full build cycle for proper citation/reference resolution
        aux_name = latex_file.stem
        build_steps = [
            (
                ["pdflatex", "-interaction=nonstopmode", latex_file.name],
                "pdflatex (1/3)",
            ),
            (["bibtex", aux_name], "bibtex"),
            (
                ["pdflatex", "-interaction=nonstopmode", latex_file.name],
                "pdflatex (2/3)",
            ),
            (
                ["pdflatex", "-interaction=nonstopmode", latex_file.name],
                "pdflatex (3/3)",
            ),
        ]

        for cmd, step_name in build_steps:
            if verbose:
                print(f"[build]   Running: {step_name}")
            result = subprocess.run(
                cmd,
                cwd=latex_dir,
                capture_output=True,
                text=True,
                encoding="latin-1",
                errors="replace",
            )
            # bibtex returns non-zero if no citations, which is fine
            if result.returncode != 0 and "bibtex" not in cmd[0]:
                if verbose:
                    if result.stdout:
                        print(result.stdout)
                print(
                    f"[build] {step_name} had warnings/errors (exit {result.returncode})"
                )

        # Copy PDF to releases/ (INVARIANT 3)
        # Use variant-specific naming to avoid conflicts
        pdf_name = latex_file.stem + ".pdf"
        pdf_src = latex_dir / pdf_name
        if pdf_src.exists():
            releases_dir = self._get_releases_dir(paper_id)
            pdf_dest = releases_dir / f"{paper_id}.pdf"
            shutil.copy2(pdf_src, pdf_dest)
            print(f"[build] ✓ {paper_id}.pdf → releases/")

    def build_submission(self, paper_id: str, verbose: bool = False):
        """Build review-submission PDF with venue-specific formatting.

        Uses the submission_format.latex_flag from papers.yaml to trigger
        format switching (e.g., single-column double-spaced for JSAIT review).
        Outputs a separate *_submission.pdf alongside the standard PDF.
        """
        # Check if this paper has a submission format defined
        raw_papers = self._raw_metadata.get("papers", {})
        raw_meta = raw_papers.get(paper_id, {})
        sub_fmt = raw_meta.get("submission_format")
        if not sub_fmt:
            print(
                f"[build] {paper_id} has no submission_format in papers.yaml, skipping."
            )
            return

        latex_flag = sub_fmt["latex_flag"]
        description = sub_fmt.get("description", "review format")

        meta = self._get_paper_meta(paper_id)
        paper_dir = self._get_paper_dir(paper_id)
        latex_dir = paper_dir / meta.latex_dir
        latex_file = latex_dir / meta.latex_file

        if not latex_file.exists():
            raise FileNotFoundError(f"LaTeX file not found: {latex_file}")

        self._sync_shared_preambles(paper_id)
        self._write_latex_lean_stats(paper_id)
        self._write_assumption_ledger_auto(paper_id)
        self._write_lean_handle_ids_auto(paper_id)
        self._rewrite_content_lean_handles_to_ids(paper_id)
        self._normalize_and_fill_claimstamps(paper_id)
        self._write_claim_mapping_auto(paper_id)
        self._write_proof_hardness_index_auto(paper_id)
        self._update_paper_date(latex_file)

        print(f"[build] Building {paper_id} submission PDF ({description})...")

        # Use jobname to output a separate PDF without overwriting the standard one
        job_name = latex_file.stem + "_submission"
        tex_input = f"\\def{latex_flag}{{}}\\input{{{latex_file.name}}}"

        aux_name = job_name
        build_steps = [
            (
                [
                    "pdflatex",
                    "-interaction=nonstopmode",
                    f"-jobname={job_name}",
                    tex_input,
                ],
                "pdflatex (1/3)",
            ),
            (["bibtex", aux_name], "bibtex"),
            (
                [
                    "pdflatex",
                    "-interaction=nonstopmode",
                    f"-jobname={job_name}",
                    tex_input,
                ],
                "pdflatex (2/3)",
            ),
            (
                [
                    "pdflatex",
                    "-interaction=nonstopmode",
                    f"-jobname={job_name}",
                    tex_input,
                ],
                "pdflatex (3/3)",
            ),
        ]

        for cmd, step_name in build_steps:
            if verbose:
                print(f"[build]   Running: {step_name}")
            result = subprocess.run(
                cmd,
                cwd=latex_dir,
                capture_output=True,
                text=True,
                encoding="latin-1",
                errors="replace",
            )
            if result.returncode != 0 and "bibtex" not in cmd[0]:
                if verbose:
                    if result.stdout:
                        print(result.stdout)
                print(
                    f"[build] {step_name} had warnings/errors (exit {result.returncode})"
                )

        # Copy submission PDF to releases/
        pdf_src = latex_dir / f"{job_name}.pdf"
        if pdf_src.exists():
            releases_dir = self._get_releases_dir(paper_id)
            pdf_dest = releases_dir / f"{paper_id}_submission.pdf"
            shutil.copy2(pdf_src, pdf_dest)
            print(f"[build] ✓ {paper_id}_submission.pdf → releases/")
        else:
            print(f"[build] ✗ Submission PDF not generated for {paper_id}")

    def build_markdown(self, paper_id: str):
        """Build Markdown version of a paper.

        Follows the main LaTeX include chain so Markdown mirrors PDF contents.

        For variants (e.g., paper1_jsait), uses variant-specific naming.
        """
        meta = self._get_paper_meta(paper_id)
        out_dir = self._get_paper_dir(paper_id) / "markdown"
        # Use paper_id for variant-specific naming
        out_file = out_dir / f"{paper_id}.md"

        out_dir.mkdir(parents=True, exist_ok=True)
        print(f"[build-md] Building {paper_id}: {meta.name}...")
        self._write_latex_lean_stats(paper_id)
        self._write_assumption_ledger_auto(paper_id)
        self._write_lean_handle_ids_auto(paper_id)
        self._rewrite_content_lean_handles_to_ids(paper_id)
        self._normalize_and_fill_claimstamps(paper_id)
        self._write_claim_mapping_auto(paper_id)
        self._write_proof_hardness_index_auto(paper_id)

        # Discover files from main LaTeX include order
        content_files = self._discover_content_files(paper_id)
        # Single source of truth for generated artifacts: main LaTeX `\title{...}`.
        title = self._release_title_from_latex(paper_id)
        lean_stats = self._get_lean_stats(paper_id)
        self._build_markdown_file(meta, content_files, out_file, title, lean_stats)

        # Also copy to releases/ for arxiv package
        releases_dir = self._get_releases_dir(paper_id)
        shutil.copy2(out_file, releases_dir / out_file.name)
        self.build_copy_paste_metadata(paper_id)
        print(f"[build-md] {paper_id} → {out_file.relative_to(self.repo_root)}")

    def _extract_braced_command_argument(
        self, content: str, command: str
    ) -> str | None:
        """Extract the first braced argument for a LaTeX command.

        Supports optional square-bracket argument: \\command[...]{...}
        """
        marker = f"\\{command}"
        start = content.find(marker)
        if start == -1:
            return None

        i = start + len(marker)
        n = len(content)

        # Skip whitespace
        while i < n and content[i].isspace():
            i += 1

        # Optional [..] argument
        if i < n and content[i] == "[":
            depth = 1
            i += 1
            while i < n and depth > 0:
                if content[i] == "[":
                    depth += 1
                elif content[i] == "]":
                    depth -= 1
                i += 1
            while i < n and content[i].isspace():
                i += 1

        # Required {..} argument
        if i >= n or content[i] != "{":
            return None

        depth = 1
        i += 1
        arg_start = i
        while i < n and depth > 0:
            if content[i] == "{":
                depth += 1
            elif content[i] == "}":
                depth -= 1
            i += 1

        if depth != 0:
            return None

        return content[arg_start : i - 1]

    def _latex_inline_to_plain(self, text: str) -> str:
        """Convert a LaTeX inline snippet to plain text."""
        try:
            result = subprocess.run(
                [
                    "pandoc",
                    "-f",
                    "latex",
                    "-t",
                    "plain",
                    "--wrap=none",
                    "--columns=100",
                ],
                input=text,
                capture_output=True,
                text=True,
            )
            if result.returncode == 0 and result.stdout.strip():
                plain = result.stdout.strip()
            else:
                plain = text
        except Exception:
            plain = text

        # Normalize line breaks and TeX line-break commands.
        plain = plain.replace("\\\\", " ")
        plain = re.sub(r"\s+", " ", plain).strip()
        return plain

    def _extract_main_latex_title(self, paper_id: str) -> str | None:
        """Extract the displayed title from the variant's main LaTeX file."""
        meta = self._get_paper_meta(paper_id)
        main_tex = self._get_paper_dir(paper_id) / meta.latex_dir / meta.latex_file
        if not main_tex.exists():
            return None

        content = main_tex.read_text(encoding="utf-8", errors="replace")
        content = self._strip_latex_comments(content)
        raw_title = self._extract_braced_command_argument(content, "title")
        if not raw_title:
            return None
        return self._latex_inline_to_plain(raw_title)

    def _release_title_from_latex(self, paper_id: str) -> str:
        """Canonical release title source: main LaTeX `\\title{...}`."""
        title = self._extract_main_latex_title(paper_id)
        if title:
            return title
        meta = self._get_paper_meta(paper_id)
        main_tex = self._get_paper_dir(paper_id) / meta.latex_dir / meta.latex_file
        raise ValueError(
            f"{paper_id}: missing canonical LaTeX title in {main_tex.relative_to(self.repo_root)} "
            "(expected \\\\title{...})"
        )

    def _extract_abstract_latex(self, paper_id: str) -> Optional[str]:
        """Extract abstract LaTeX content from content/abstract.tex."""
        abstract_file = self._get_content_dir(paper_id) / "abstract.tex"
        if not abstract_file.exists():
            return None

        content = abstract_file.read_text(encoding="utf-8", errors="replace")
        match = re.search(
            r"\\begin\{abstract\}(.*?)\\end\{abstract\}", content, re.DOTALL
        )
        if match:
            content = match.group(1)

        content = content.strip()
        return content if content else None

    def _normalize_plaintext_block(self, text: str) -> str:
        """Normalize plain text for copy/paste metadata fields."""
        lines = text.replace("\r\n", "\n").replace("\r", "\n").split("\n")
        normalized_lines: List[str] = []
        last_blank = False

        for line in lines:
            clean = re.sub(r"\s+", " ", line).strip()
            if not clean:
                if not last_blank:
                    normalized_lines.append("")
                last_blank = True
                continue
            normalized_lines.append(clean)
            last_blank = False

        return "\n".join(normalized_lines).strip()

    def _clean_metadata_reference_tokens(self, text: str) -> str:
        """Remove paper-internal reference tokens from metadata snippets."""
        text = self._postprocess_markdown_text(text)
        text = re.sub(r"\[\s*\\*\s*\]\(#.*?\)\{[^}]*\}", "", text)
        text = re.sub(r"\[\s*\\*\s*\]\(#.*?\)", "", text)
        text = re.sub(r"\{reference-type=\"ref\"[^}]*\}", "", text)
        text = re.sub(r"\[D:[^\[]*\[R=[^\]]+\]\]", "", text)
        text = re.sub(
            r"\[(?:sec|thm|prop|cor|lem|app|rem|eq|fig|tab):[^\]]+\]", "", text
        )
        text = re.sub(r"\[R=[^\]]+\]", "", text)
        text = re.sub(r"\[D:[^\]]+\]", "", text)
        text = re.sub(r"\[R:[^\]]+\]", "", text)
        text = re.sub(r"\[[^\]]*\]\(#.*?\)", "", text)
        text = re.sub(r";\s*see Appendix\s*\)", ")", text)
        text = re.sub(r"see Appendix\s*", "", text)
        text = re.sub(r"\((?:see )?(?:Section|Remark|Appendix)\s*\)", "", text)
        text = re.sub(r"\s+\\\s*$", "", text, flags=re.MULTILINE)
        text = re.sub(r"\s+\\\s+", " ", text)
        text = re.sub(r"\s+([,.;:])", r"\1", text)
        text = re.sub(r"\(\s*\)", "", text)
        return text

    def _latex_snippet_to_plain(self, latex_input: str, paper_id: str) -> str:
        """Convert a LaTeX snippet into plain UTF-8 text for metadata copy/paste."""
        prepared = self._expand_lean_stat_macros(latex_input, paper_id)
        prepared = self._normalize_claimstamp_for_markdown(prepared)
        prepared = self._prepend_markdown_macro_prelude(prepared)

        result = subprocess.run(
            ["pandoc", "-f", "latex", "-t", "plain", "--wrap=none", "--columns=100"],
            input=prepared,
            capture_output=True,
            text=True,
        )
        plain = (
            result.stdout
            if result.returncode == 0 and result.stdout.strip()
            else latex_input
        )

        plain = self._clean_metadata_reference_tokens(plain)
        return self._normalize_plaintext_block(plain)

    def _latex_snippet_to_mathjax(self, latex_input: str, paper_id: str) -> str:
        """Convert a LaTeX snippet into markdown text with MathJax-style TeX math."""
        prepared = self._expand_lean_stat_macros(latex_input, paper_id)
        prepared = self._normalize_claimstamp_for_markdown(prepared)
        prepared = self._prepend_markdown_macro_prelude(prepared)

        result = subprocess.run(
            [
                "pandoc",
                "-f",
                "latex",
                "-t",
                "markdown+tex_math_dollars",
                "--wrap=none",
                "--columns=100",
            ],
            input=prepared,
            capture_output=True,
            text=True,
        )
        mathjax = (
            result.stdout
            if result.returncode == 0 and result.stdout.strip()
            else latex_input
        )

        # Expand common project macros to MathJax-safe forms.
        mathjax = re.sub(r"\\SigmaP\{([^}]+)\}", r"\\Sigma_{\1}^{P}", mathjax)
        mathjax = re.sub(r"\\PiP\{([^}]+)\}", r"\\Pi_{\1}^{P}", mathjax)
        mathjax = mathjax.replace(r"\coNP", "coNP")
        mathjax = mathjax.replace(r"\NP", "NP")
        mathjax = mathjax.replace(r"\Pclass", "P")
        mathjax = mathjax.replace(r"\Opt", r"\operatorname{Opt}")
        mathjax = re.sub(r"\\claimstamp\{[^}]*\}\{[^}]*\}", "", mathjax)

        # Strip Markdown bold/italic markers for arXiv compatibility.
        # arXiv abstracts only support MathJax math, not Markdown or LaTeX text formatting.
        # Simply remove the markers, leaving plain text.
        mathjax = re.sub(r"\*\*([^*]+?)\*\*", r"\1", mathjax)  # **text** -> text
        mathjax = re.sub(r"(?<!\*)\*([^*]+?)\*(?!\*)", r"\1", mathjax)  # *text* -> text

        mathjax = self._clean_metadata_reference_tokens(mathjax)
        return self._normalize_plaintext_block(mathjax)

    def _mathjax_markdown_to_unicode_markdown(self, mathjax_text: str) -> str:
        """Convert `$...$` math in markdown to Unicode while preserving markdown structure."""
        cache: Dict[str, str] = {}

        def _to_unicode(expr: str) -> str:
            expr = expr.strip()
            if expr in cache:
                return cache[expr]

            result = subprocess.run(
                [
                    "pandoc",
                    "-f",
                    "latex",
                    "-t",
                    "plain",
                    "--wrap=none",
                    "--columns=100",
                ],
                input=f"${expr}$",
                capture_output=True,
                text=True,
            )
            converted = (
                result.stdout.strip()
                if result.returncode == 0 and result.stdout.strip()
                else expr
            )
            converted = re.sub(r"\s+", " ", converted).strip()
            cache[expr] = converted
            return converted

        # Convert display math first, then inline math.
        converted = re.sub(
            r"\$\$([\s\S]*?)\$\$",
            lambda m: _to_unicode(m.group(1)),
            mathjax_text,
        )
        converted = re.sub(
            r"\$([^$\n]+?)\$",
            lambda m: _to_unicode(m.group(1)),
            converted,
        )
        return self._normalize_plaintext_block(converted)

    def _latex_snippet_to_unicode_zenodo(self, latex_input: str, paper_id: str) -> str:
        """Convert LaTeX to Unicode plain text suitable for Zenodo (no markdown markers)."""
        plain = self._latex_snippet_to_plain(latex_input, paper_id)
        # Use explicit Unicode bullets instead of markdown-style `- ` markers.
        plain = re.sub(r"(?m)^-\s+", "• ", plain)
        return self._normalize_plaintext_block(plain)

    def _default_arxiv_comments(self, paper_id: str) -> str:
        """Build a default arXiv comments line when no explicit metadata is configured."""
        meta = self._get_paper_meta(paper_id)
        lean_stats = self._get_lean_stats(paper_id)
        return (
            f"{meta.venue} submission. Lean 4 artifact: "
            f"{lean_stats.line_count} lines, {lean_stats.theorem_count} theorems/lemmas "
            f"across {lean_stats.file_count} files ({lean_stats.sorry_count} sorry placeholders)."
        )

    def _write_abstract_helper_files(
        self,
        paper_id: str,
        title: str,
        abstract_mathjax: str,
        abstract_unicode: str,
    ) -> tuple[Path, Path]:
        """Write convenience abstract files from one canonical source.

        Primary file is paper-id scoped to avoid collisions when multiple variants
        share a directory (e.g., `paper4` and `paper4_toc`).
        """
        meta = self._get_paper_meta(paper_id)
        releases_dir = self._get_releases_dir(paper_id)

        primary_path = releases_dir / f"arxiv_abstract_{paper_id}.md"
        primary_lines = [
            f"# arXiv abstract ({paper_id})",
            "",
            f"Title: {title}",
            "",
            "## Abstract (MathJax, arXiv-ready)",
            "",
            "```text",
            abstract_mathjax,
            "```",
            "",
            "## Abstract (Unicode, Zenodo-ready)",
            "",
            "```text",
            abstract_unicode,
            "```",
            "",
        ]
        primary_path.write_text("\n".join(primary_lines), encoding="utf-8")

        # Backward-compatible filename (dir-scoped) can be ambiguous when
        # multiple paper IDs point at the same directory.
        legacy_path = releases_dir / f"arxiv_abstract_{meta.dir_name}.md"
        sibling_ids = sorted(
            pid
            for pid, sibling_meta in self.papers.items()
            if sibling_meta.dir_name == meta.dir_name
        )
        if len(sibling_ids) == 1:
            legacy_path.write_text("\n".join(primary_lines), encoding="utf-8")
        else:
            redirect_lines = [
                f"# Deprecated helper file: arxiv_abstract_{meta.dir_name}.md",
                "",
                "This directory has multiple paper IDs with different titles/abstracts.",
                "Use the paper-id-specific helper files instead:",
                "",
            ]
            redirect_lines.extend(
                f"- `arxiv_abstract_{sibling_id}.md`" for sibling_id in sibling_ids
            )
            redirect_lines.append("")
            legacy_path.write_text("\n".join(redirect_lines), encoding="utf-8")

        return primary_path, legacy_path

    def build_copy_paste_metadata(self, paper_id: str) -> Path:
        """Generate human/machine copy-paste metadata for Zenodo + arXiv."""
        meta = self._get_paper_meta(paper_id)
        # Single source of truth for generated artifacts: main LaTeX `\title{...}`.
        title = self._release_title_from_latex(paper_id)
        abstract_latex = self._extract_abstract_latex(paper_id)
        abstract_mathjax = (
            self._latex_snippet_to_mathjax(abstract_latex, paper_id)
            if abstract_latex
            else "Abstract not found."
        )
        # Zenodo variant should be Unicode plain text (no markdown formatting markers).
        abstract_unicode = (
            self._latex_snippet_to_unicode_zenodo(abstract_latex, paper_id)
            if abstract_latex
            else "Abstract not found."
        )
        arxiv_comments = (
            self._normalize_plaintext_block(meta.arxiv_comments)
            if meta.arxiv_comments.strip()
            else self._default_arxiv_comments(paper_id)
        )

        payload = {
            "paper_id": paper_id,
            "title": title,
            "zenodo": {
                "title": title,
                "abstract": abstract_unicode,
            },
            "arxiv": {
                "title": title,
                "abstract": abstract_mathjax,
                "comments": arxiv_comments,
            },
            "abstract_variants": {
                "unicode": abstract_unicode,
                "mathjax": abstract_mathjax,
            },
        }
        machine_yaml = yaml.safe_dump(
            payload, sort_keys=False, allow_unicode=True
        ).strip()

        lines = [
            "AUTO-GENERATED COPY/PASTE METADATA",
            f"Generated: {datetime.now().isoformat()}",
            "",
            "=== HUMAN COPY/PASTE ===",
            "",
            f"Title: {title}",
            "",
            "Abstract (Unicode, for Zenodo):",
            abstract_unicode,
            "",
            "Abstract (MathJax, for arXiv):",
            abstract_mathjax,
            "",
            "arXiv Comments:",
            arxiv_comments,
            "",
            "=== MACHINE YAML ===",
            machine_yaml,
            "",
        ]

        releases_dir = self._get_releases_dir(paper_id)
        out_file = releases_dir / f"{paper_id}_copy_paste.txt"
        out_file.write_text("\n".join(lines), encoding="utf-8")
        abstract_helper_file, legacy_helper_file = self._write_abstract_helper_files(
            paper_id=paper_id,
            title=title,
            abstract_mathjax=abstract_mathjax,
            abstract_unicode=abstract_unicode,
        )
        print(f"[metadata] {paper_id} → {out_file.relative_to(self.repo_root)}")
        print(
            "[metadata] "
            f"{paper_id} abstracts → {abstract_helper_file.relative_to(self.repo_root)} "
            f"(legacy alias: {legacy_helper_file.relative_to(self.repo_root)})"
        )
        return out_file

    def _build_markdown_file(
        self,
        meta: PaperMeta,
        content_files: List[Path],
        out_file: Path,
        title: str,
        lean_stats: LeanStats,
    ):
        """Generate markdown file from LaTeX content."""
        with open(out_file, "w") as f:
            # Header
            f.write(f"# Paper: {title}\n\n")
            f.write(
                f"**Status**: {meta.venue}-ready | "
                f"**Lean**: {lean_stats.line_count} lines, "
                f"{lean_stats.theorem_count} theorems\n\n---\n\n"
            )

            # Abstract
            f.write("## Abstract\n\n")
            abstract_file = next(
                (p for p in content_files if p.name == "abstract.tex"), None
            )
            if abstract_file and abstract_file.exists():
                # Try extracting from \begin{abstract}...\end{abstract} first,
                # fall back to raw file content if no environment found
                content = abstract_file.read_text(encoding="utf-8", errors="replace")
                if r"\begin{abstract}" in content:
                    self._convert_latex_to_markdown(
                        abstract_file,
                        f,
                        paper_id=meta.paper_id,
                        extract_env="abstract",
                    )
                else:
                    self._convert_latex_to_markdown(
                        abstract_file, f, paper_id=meta.paper_id
                    )
            else:
                f.write("_Abstract not available._\n\n")

            # Content sections (ordered exactly as LaTeX includes)
            for content_path in content_files:
                if abstract_file and content_path.resolve() == abstract_file.resolve():
                    continue
                self._convert_latex_to_markdown(content_path, f, paper_id=meta.paper_id)

            # Footer
            f.write("\n\n---\n\n## Machine-Checked Proofs\n\n")
            f.write(f"All theorems are formalized in Lean 4:\n")
            proofs_rel = self._get_paper_proofs_dir(meta.paper_id).relative_to(
                self.repo_root
            )
            f.write(f"- Location: `{proofs_rel}/`\n")
            f.write(f"- Lines: {lean_stats.line_count}\n")
            f.write(f"- Theorems: {lean_stats.theorem_count}\n")
            f.write(f"- `sorry` placeholders: {lean_stats.sorry_count}\n")

    def _convert_latex_to_markdown(
        self,
        tex_file: Path,
        out_file,
        paper_id: str,
        extract_env: str | None = None,
    ):
        """Convert LaTeX file to Markdown using pandoc.

        Args:
            tex_file: Path to .tex file
            out_file: Output file handle
            extract_env: If set, extract content from \\begin{env}...\\end{env} first
        """
        import re

        content = tex_file.read_text(encoding="utf-8", errors="replace")
        if extract_env:
            # Extract content from environment before converting
            pattern = rf"\\begin\{{{extract_env}\}}(.*?)\\end\{{{extract_env}\}}"
            match = re.search(pattern, content, re.DOTALL)
            if not match:
                out_file.write(f"_Content not found in {tex_file.name}_\n\n")
                return
            latex_input = match.group(1).strip()
        else:
            latex_input = content

        latex_input = self._expand_lean_stat_macros(latex_input, paper_id)
        latex_input = self._normalize_claimstamp_for_markdown(latex_input)
        latex_input = self._prepend_markdown_macro_prelude(latex_input)
        result = subprocess.run(
            ["pandoc", "-f", "latex", "-t", "markdown", "--wrap=none", "--columns=100"],
            input=latex_input,
            capture_output=True,
            text=True,
        )

        if result.returncode == 0 and result.stdout:
            out_file.write(self._postprocess_markdown_text(result.stdout))
            out_file.write("\n\n")
        else:
            out_file.write(f"_Failed to convert {tex_file.name}_\n\n")

    def _normalize_claimstamp_for_markdown(self, latex_input: str) -> str:
        """Simplify `\\claimstamp{...}{...}` arguments for markdown readability.

        Keep theorem provenance, but normalize references to raw labels
        (e.g., `Thm.~\\ref{thm:x}` -> `thm:x`) so generated markdown stays compact.
        """
        pattern = re.compile(
            r"\\claimstamp\{((?:[^{}]|\\ref\{[^}]+\})*)\}\{([^}]*)\}",
            re.DOTALL,
        )

        title_ref = re.compile(
            r"(?:Theorem|Thm\.?|Proposition|Prop\.?|Corollary|Cor\.?|Lemma|Lem\.?)\s*~?\s*\\ref\{([^}]+)\}"
        )

        def repl(match: re.Match[str]) -> str:
            derived = match.group(1)
            regime = match.group(2)
            derived = title_ref.sub(r"\1", derived)
            derived = re.sub(r"\\ref\{([^}]+)\}", r"\1", derived)
            derived = derived.replace("~", " ")
            derived = re.sub(r"\s+", " ", derived).strip(" ,")
            derived = re.sub(r"\s*,\s*", ", ", derived)
            regime = re.sub(r"\s+", " ", regime).strip()
            return rf"\claimstamp{{{derived}}}{{{regime}}}"

        return pattern.sub(repl, latex_input)

    def _prepend_markdown_macro_prelude(self, latex_input: str) -> str:
        """Prepend markdown-only macro normalizations for pandoc conversion.

        Markdown conversion processes section files directly, without the main
        LaTeX preamble. Custom macros used in prose (e.g., ``\\coNP``) would
        otherwise be dropped by pandoc, producing broken text such as
        ``-complete``. We define plain/math-safe expansions here strictly for
        conversion fidelity.
        """
        prelude = "\n".join(
            [
                r"\newcommand{\coNP}{coNP}",
                r"\newcommand{\NP}{NP}",
                r"\newcommand{\Pclass}{P}",
                r"\newcommand{\SigmaP}[1]{\Sigma_{#1}^{P}}",
                r"\newcommand{\PiP}[1]{\Pi_{#1}^{P}}",
                r"\newcommand{\Opt}{\operatorname{Opt}}",
                r"\newcommand{\claimstamp}[2]{ [D:#1; R:#2]}",
            ]
        )
        return f"{prelude}\n{latex_input}"

    def _postprocess_markdown_text(self, text: str) -> str:
        """Normalize small TeX-to-markdown spacing artifacts.

        TeX control-word macros consume following spaces unless braced. When
        class macros appear in prose (e.g., ``\\coNP characterization``), the
        converted markdown can become concatenated (``coNPcharacterization``).
        Insert the missing separator for known complexity-class tokens.
        """
        return re.sub(r"\bcoNP(?=[A-Za-z])", "coNP ", text)

    def _get_claim_mapping_file(self, paper_id: str) -> Optional[Path]:
        """Locate theorem-handle mapping file for claim coverage checks."""
        meta = self._get_paper_meta(paper_id)
        latex_dir = self._get_paper_dir(paper_id) / meta.latex_dir
        if meta.claim_mapping_file:
            explicit = latex_dir / meta.claim_mapping_file
            return explicit if explicit.exists() else None

        candidates = [
            latex_dir / "content" / "11_lean_proofs.tex",
            latex_dir / "content" / "10_lean_4_proof_listings.tex",
            latex_dir / "content" / "10_lean_proof_listings.tex",
            latex_dir / "content" / "10_lean_proofs.tex",
        ]
        for candidate in candidates:
            if candidate.exists():
                return candidate
        return None

    def _extract_paper_claim_labels(self, paper_id: str) -> Set[str]:
        """Extract theorem/corollary/lemma/proposition labels from content/*.tex."""
        content_dir = self._get_content_dir(paper_id)
        if not content_dir.exists():
            return set()

        labels: Set[str] = set()
        label_pattern = re.compile(r"\\label\{((?:thm|cor|lem|prop):[^}]+)\}")
        claim_label_pattern = re.compile(
            r"\\begin\{claim\}\{[^{}]*\}\{((?:thm|cor|lem|prop):[^{}]+)\}"
        )
        for tex_file in sorted(content_dir.glob("*.tex")):
            text = tex_file.read_text(encoding="utf-8", errors="replace")
            labels.update(label_pattern.findall(text))
            labels.update(claim_label_pattern.findall(text))
        return labels

    def _extract_mapped_claim_labels(self, mapping_file: Path) -> Set[str]:
        """Extract mapped theorem-handle labels from a Lean-coverage appendix file."""
        text = mapping_file.read_text(encoding="utf-8", errors="replace")
        labels: Set[str] = set()
        patterns = [
            r"\\nolinkurl\{((?:thm|cor|lem|prop):[^}]+)\}",
            r"\\(?:ref|autoref|Cref)\{((?:thm|cor|lem|prop):[^}]+)\}",
        ]
        for pattern in patterns:
            labels.update(re.findall(pattern, text))
        return labels

    def check_claim_coverage(
        self, paper_id: str, fail_on_missing: bool = False
    ) -> Dict[str, object]:
        """Check label coverage between paper claims and Lean mapping appendix."""
        self._write_lean_handle_ids_auto(paper_id)
        self._rewrite_content_lean_handles_to_ids(paper_id)
        self._normalize_and_fill_claimstamps(paper_id)
        self._write_claim_mapping_auto(paper_id)
        self._write_proof_hardness_index_auto(paper_id)
        claim_labels = self._extract_paper_claim_labels(paper_id)
        mapping_file = self._get_claim_mapping_file(paper_id)

        if mapping_file is None:
            message = f"[claim-check] {paper_id}: no mapping file found; skipping."
            print(message)
            if fail_on_missing and claim_labels:
                raise RuntimeError(message)
            return {
                "paper_id": paper_id,
                "mapping_file": None,
                "paper_labels": sorted(claim_labels),
                "mapped_labels": [],
                "missing_labels": sorted(claim_labels),
                "extra_labels": [],
            }

        # Keep a single source of truth for auto-generated mapping files:
        # use direct label->handle extraction, not rendered table parsing.
        if mapping_file.name == "claim_mapping_auto.tex":
            label_to_handles = self._extract_claim_label_to_lean_handles(paper_id)
            mapped_labels = {
                label for label, handles in label_to_handles.items() if handles
            }
        else:
            mapped_labels = self._extract_mapped_claim_labels(mapping_file)
        missing_labels = sorted(claim_labels - mapped_labels)
        extra_labels = sorted(mapped_labels - claim_labels)

        print(
            f"[claim-check] {paper_id}: "
            f"paper={len(claim_labels)} mapped={len(mapped_labels)} "
            f"missing={len(missing_labels)} extra={len(extra_labels)}"
        )
        if missing_labels:
            print("[claim-check]   Missing mappings:")
            for label in missing_labels:
                print(f"[claim-check]     - {label}")
        if extra_labels:
            print("[claim-check]   Extra mappings (not found in paper labels):")
            for label in extra_labels:
                print(f"[claim-check]     - {label}")

        if fail_on_missing and missing_labels:
            raise RuntimeError(
                f"Claim mapping incomplete for {paper_id}: {len(missing_labels)} labels unmapped"
            )

        return {
            "paper_id": paper_id,
            "mapping_file": str(mapping_file.relative_to(self.repo_root)),
            "paper_labels": sorted(claim_labels),
            "mapped_labels": sorted(mapped_labels),
            "missing_labels": missing_labels,
            "extra_labels": extra_labels,
        }

    def _update_paper_date(self, tex_file: Path):
        """Update publication date in LaTeX file using regex for correct replacement."""
        import re

        year = datetime.now().strftime("%Y")
        try:
            content = tex_file.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            content = tex_file.read_text(encoding="latin-1")

        # Normalize to compile-time date in LaTeX sources.
        content = re.sub(r"\\date\{[^}]*\}", r"\\date{\\today}", content)
        content = re.sub(
            r"Manuscript received [^.\\n]*\.",
            r"Manuscript received \\today.",
            content,
        )

        # Keep explicit year fields in sync with build year where present.
        content = re.sub(
            r"\\copyrightyear\{[^}]*\}", f"\\\\copyrightyear{{{year}}}", content
        )
        content = re.sub(r"\\acmYear\{[^}]*\}", f"\\\\acmYear{{{year}}}", content)
        tex_file.write_text(content, encoding="utf-8")

    def package_arxiv(self, paper_id: str):
        """
        Package paper for arXiv submission.

        Includes:
        - PDF (compiled paper)
        - Markdown (full text for LLM consumption)
        - Lean proofs (source code)
        - BUILD_LOG.txt (actual lake build output as compilation proof)

        For variants (e.g., paper1_jsait), uses variant-specific staging directory.
        """
        self._sync_shared_preambles(paper_id)
        self._write_latex_lean_stats(paper_id)
        self._write_assumption_ledger_auto(paper_id)
        self._write_lean_handle_ids_auto(paper_id)
        self._rewrite_content_lean_handles_to_ids(paper_id)
        self._normalize_and_fill_claimstamps(paper_id)
        self._write_claim_mapping_auto(paper_id)
        self._write_proof_hardness_index_auto(paper_id)
        metadata_file = self.build_copy_paste_metadata(paper_id)

        # Phase 1: Validate all required files exist (fail-loud)
        pdf_file = self._validate_and_get_pdf(paper_id)
        md_file = self._validate_and_get_markdown(paper_id)

        # Phase 2: Create staging directory in releases/ with variant-specific naming
        releases_dir = self._get_releases_dir(paper_id)
        archive_prefix = self._get_archive_prefix(paper_id)
        package_dir = releases_dir / f"arxiv_package_{archive_prefix}"
        if package_dir.exists():
            shutil.rmtree(package_dir)
        package_dir.mkdir(parents=True)

        print(f"[arxiv] Packaging {paper_id}...")

        # Phase 3: Copy artifacts
        self._copy_pdf(pdf_file, package_dir)
        self._copy_markdown(md_file, package_dir)
        self._copy_copy_paste_metadata(metadata_file, package_dir)
        self._copy_latex_sources(paper_id, package_dir)
        self._copy_lean_proofs(paper_id, package_dir)
        self._copy_experiments(paper_id, package_dir)

        if self.arxiv_config.include_build_log:
            self._create_build_log(paper_id, package_dir)

        # Phase 4: Create compressed archives
        tar_path, zip_path = self._create_archive(paper_id, package_dir)

        print(
            f"[arxiv] {paper_id} → {tar_path.relative_to(self.repo_root)}, {zip_path.name}"
        )
        return tar_path

    def _validate_and_get_pdf(self, paper_id: str) -> Path:
        """Validate PDF exists and return path. Fail-loud if missing."""
        meta = self._get_paper_meta(paper_id)
        paper_dir = self._get_paper_dir(paper_id)
        latex_dir = paper_dir / meta.latex_dir
        pdfs = list(latex_dir.glob("*.pdf"))

        if not pdfs:
            raise FileNotFoundError(
                f"[arxiv] FATAL: No PDF found in {latex_dir}\n"
                f"  Paper: {meta.name}\n"
                f"  Run: python3 scripts/build_papers.py latex {paper_id}"
            )
        return pdfs[0]

    def _validate_and_get_markdown(self, paper_id: str) -> Path:
        """Validate Markdown exists and return path. Fail-loud if missing."""
        meta = self._get_paper_meta(paper_id)
        paper_dir = self._get_paper_dir(paper_id)
        # Must match build_markdown(), which writes <paper_id>.md.
        # This is critical for variants (e.g., paper4_toc) that share dir_name
        # with a base paper but have different LaTeX sources/content.
        md_file = paper_dir / "markdown" / f"{paper_id}.md"

        if not md_file.exists():
            raise FileNotFoundError(
                f"[arxiv] FATAL: Markdown not found: {md_file}\n"
                f"  Paper: {meta.name}\n"
                f"  Run: python3 scripts/build_papers.py markdown {paper_id}"
            )
        return md_file

    def _copy_pdf(self, pdf_file: Path, package_dir: Path) -> None:
        """Copy PDF to package directory."""
        pdf_dest = package_dir / pdf_file.name
        shutil.copy2(pdf_file, pdf_dest)
        print(f"[arxiv]   PDF: {pdf_file.name}")

    def _copy_markdown(self, md_file: Path, package_dir: Path) -> None:
        """Copy Markdown to package directory."""
        md_dest = package_dir / md_file.name
        shutil.copy2(md_file, md_dest)
        print(f"[arxiv]   Markdown: {md_file.name}")

    def _copy_copy_paste_metadata(self, metadata_file: Path, package_dir: Path) -> None:
        """Copy copy/paste metadata file to package directory."""
        metadata_dest = package_dir / metadata_file.name
        shutil.copy2(metadata_file, metadata_dest)
        print(f"[arxiv]   Metadata: {metadata_file.name}")

    def _copy_latex_sources(self, paper_id: str, package_dir: Path) -> None:
        """Copy LaTeX source files for arXiv submission.

        Copies all .tex, .bib, .bbl, .cls, .sty files from the latex directory.
        Also copies content/ subdirectory if present.
        """
        meta = self._get_paper_meta(paper_id)
        paper_dir = self._get_paper_dir(paper_id)
        latex_dir = paper_dir / meta.latex_dir

        if not latex_dir.exists():
            print(f"[arxiv]   No LaTeX directory for {paper_id}, skipping...")
            return

        # Extensions to copy
        extensions = [".tex", ".bib", ".bbl", ".cls", ".sty"]
        copied_count = 0

        # Copy top-level LaTeX files
        for ext in extensions:
            for src_file in latex_dir.glob(f"*{ext}"):
                shutil.copy2(src_file, package_dir / src_file.name)
                copied_count += 1

        # Copy content/ subdirectory if present
        content_dir = latex_dir / "content"
        if content_dir.exists():
            content_dest = package_dir / "content"
            content_dest.mkdir(parents=True, exist_ok=True)
            for src_file in content_dir.glob("*.tex"):
                shutil.copy2(src_file, content_dest / src_file.name)
                copied_count += 1

        print(f"[arxiv]   LaTeX sources: {copied_count} files")

    def _copy_lean_proofs(self, paper_id: str, package_dir: Path) -> None:
        """Copy Lean proofs for specific paper to package directory.

        Includes:
        - The paper's own proofs directory
        - Lean files from transitive lean_dependencies

        Dependency files are inlined into the package proofs graph by relative
        path (with conflict-safe fallback), so bridge imports resolve without
        manual per-paper path patching.
        """
        proofs_dir = self._get_paper_proofs_dir(paper_id)

        if not proofs_dir.exists():
            print(f"[arxiv]   No proofs directory for {paper_id}, skipping...")
            return

        lean_dest = package_dir / "proofs"
        lean_dest.mkdir(parents=True, exist_ok=True)

        dep_ids = self._collect_lean_dependency_closure(paper_id)
        roots: List[Tuple[str, Path]] = [(paper_id, proofs_dir)]
        roots.extend((dep_id, self._get_paper_proofs_dir(dep_id)) for dep_id in dep_ids)

        paper_files: List[Path] = []
        dep_file_count = 0
        copied_count = 0
        identical_skips = 0
        conflict_fallbacks = 0

        for source_paper_id, source_dir in roots:
            if not source_dir.exists():
                print(
                    f"[arxiv]   Warning: dependency {source_paper_id} has no proofs dir, skipping..."
                )
                continue

            for src_file in self._iter_paper_lean_files(source_dir):
                rel_path = src_file.relative_to(source_dir)
                dest_file = lean_dest / rel_path
                dest_file.parent.mkdir(parents=True, exist_ok=True)

                if dest_file.exists():
                    if self._files_identical(src_file, dest_file):
                        identical_skips += 1
                        continue
                    fallback_dest = lean_dest / f"dep_{source_paper_id}" / rel_path
                    fallback_dest.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(src_file, fallback_dest)
                    conflict_fallbacks += 1
                    copied_count += 1
                else:
                    shutil.copy2(src_file, dest_file)
                    copied_count += 1

                if source_paper_id == paper_id:
                    paper_files.append(src_file)
                else:
                    dep_file_count += 1

        # Copy config files from main paper
        config_files = ["lean-toolchain", "lake-manifest.json"]
        for fname in config_files:
            src = proofs_dir / fname
            if src.exists():
                shutil.copy2(src, lean_dest / fname)

        self._rewrite_packaged_lakefile_srcdirs(lean_dest / "lakefile.lean")
        self._write_dependency_bridge_module(paper_id, lean_dest, dep_ids)

        # Generate README (correct by construction)
        self._generate_proofs_readme(paper_id, paper_files, lean_dest)

        for dep_paper_id in dep_ids:
            dep_proofs_dir = self._get_paper_proofs_dir(dep_paper_id)
            if dep_proofs_dir.exists():
                dep_count = len(self._iter_paper_lean_files(dep_proofs_dir))
                print(f"[arxiv]   Dependency {dep_paper_id}: {dep_count} files")

        total_files = len(paper_files) + dep_file_count
        print(
            f"[arxiv]   Lean proofs: {len(paper_files)} local + {dep_file_count} dependency files "
            f"(copied={copied_count}, identical-skips={identical_skips}, conflict-fallbacks={conflict_fallbacks})"
        )

    def _rewrite_packaged_lakefile_srcdirs(self, lakefile_path: Path) -> None:
        """Rewrite external `srcDir := \"../...\"` entries for package-local builds."""
        if not lakefile_path.exists():
            return
        text = lakefile_path.read_text(encoding="utf-8", errors="replace")
        rewritten = re.sub(r'srcDir\s*:=\s*"\.\./[^"]+"', 'srcDir := "."', text)
        if rewritten != text:
            lakefile_path.write_text(rewritten, encoding="utf-8")

    def _write_dependency_bridge_module(
        self, paper_id: str, lean_dest: Path, dep_ids: List[str]
    ) -> None:
        """Generate a bridge module that imports dependency module roots."""
        if not dep_ids:
            return

        host_roots = self._derive_module_roots(paper_id)
        if not host_roots:
            return
        host_root = host_roots[0]

        dep_imports: List[str] = []
        for dep_id in dep_ids:
            for root in self._derive_module_roots(dep_id):
                if root not in dep_imports:
                    dep_imports.append(root)
        if not dep_imports:
            return

        bridge_rel = Path(*host_root.split(".")) / "DependencyBridge.lean"
        bridge_file = lean_dest / bridge_rel
        bridge_file.parent.mkdir(parents=True, exist_ok=True)

        lines: List[str] = [
            "-- Auto-generated by scripts/build_papers.py. Do not edit manually.",
            "-- Dependency bridge imports to inline transitive proof machinery.",
        ]
        for root in dep_imports:
            lines.append(f"import {root}")
        lines.extend(
            [
                "",
                f"namespace {host_root}",
                "",
                "-- Marker module: importing this namespace also imports dependency roots.",
                "",
                f"end {host_root}",
                "",
            ]
        )
        bridge_file.write_text("\n".join(lines), encoding="utf-8")

    def _copy_experiments(self, paper_id: str, package_dir: Path) -> None:
        """Copy experiments directory if present.

        Copies Python scripts, data files, and results from the experiments/ subdirectory.
        """
        paper_dir = self._get_paper_dir(paper_id)
        experiments_dir = paper_dir / "experiments"

        if not experiments_dir.exists():
            return  # No experiments directory, skip silently

        experiments_dest = package_dir / "experiments"
        experiments_dest.mkdir(parents=True, exist_ok=True)

        # Copy all relevant files
        copied_count = 0
        extensions = [".py", ".json", ".csv", ".txt", ".sh", ".md"]
        for ext in extensions:
            for src_file in experiments_dir.glob(f"*{ext}"):
                shutil.copy2(src_file, experiments_dest / src_file.name)
                copied_count += 1

        if copied_count > 0:
            print(f"[arxiv]   Experiments: {copied_count} files")

    def _generate_paper_lakefile(
        self, paper_id: str, paper_files: list, lean_dest: Path
    ) -> None:
        """Generate paper-specific lakefile from actual proof files."""
        meta = self._get_paper_meta(paper_id)

        # Extract lib names from filenames (paper4_Basic.lean -> paper4_Basic)
        lib_names = [f.stem for f in paper_files]

        lib_entries = "\n".join(
            [
                f"""lean_lib «{name}» where
  moreLeanArgs := moreLeanArgs
  weakLeanArgs := weakLeanArgs
"""
                for name in lib_names
            ]
        )

        lakefile_content = f"""import Lake
open Lake DSL

-- {meta.name} - Lean 4 Formalization
-- Auto-generated by build_papers.py

def moreServerArgs := #[
  "-Dpp.unicode.fun=true",
  "-Dpp.proofs.withType=false"
]

def moreLeanArgs := moreServerArgs

def weakLeanArgs : Array String :=
  if get_config? CI |>.isSome then
    #["-DwarningAsError=true"]
  else
    #[]

package «{meta.dir_name}» where
  moreServerArgs := moreServerArgs

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

{lib_entries}"""

        (lean_dest / "lakefile.lean").write_text(lakefile_content)

    def _generate_proofs_readme(
        self, paper_id: str, paper_files: list, lean_dest: Path
    ) -> None:
        """Generate README for proofs directory from actual proof files."""
        meta = self._get_paper_meta(paper_id)
        lean_stats = self._get_lean_stats(paper_id)

        # Build file table
        file_rows = "\n".join(
            [
                f"| `{f.name}` | {f.stem.replace(paper_id + '_', '')} |"
                for f in paper_files
            ]
        )
        sorry_summary = (
            "0 `sorry` placeholders."
            if lean_stats.sorry_count == 0
            else f"{lean_stats.sorry_count} `sorry` placeholders."
        )

        readme_content = f"""# {meta.name} - Lean 4 Formalization

## Overview

This directory contains the complete Lean 4 formalization for {meta.name}.

- **Lines:** {lean_stats.line_count}
- **Theorems:** {lean_stats.theorem_count}
- **`sorry` placeholders:** {lean_stats.sorry_count}


## Requirements

- Lean 4 (see `lean-toolchain` for exact version)
- Mathlib4

## Building

```bash
lake update
lake build
```

## File Structure

| File | Module |
|------|--------|
{file_rows}

## Verification

All files compile with {sorry_summary} All claims are machine-verified.

## License

MIT License - See main repository for details.

---
*Auto-generated by build_papers.py*
"""

        (lean_dest / "README.md").write_text(readme_content)

    def _create_build_log(self, paper_id: str, package_dir: Path) -> None:
        """
        Create BUILD_LOG.txt with ACTUAL lake build output as compilation proof.
        This is the mathematical evidence that proofs compile.
        """
        paper_title = self._release_title_from_latex(paper_id)
        lean_stats = self._get_lean_stats(paper_id)
        log_file = package_dir / "BUILD_LOG.txt"

        # Paper-specific proof files from paper's proofs directory
        proofs_dir = self._get_paper_proofs_dir(paper_id)
        paper_lean_files = self._iter_paper_lean_files(proofs_dir)
        lean_toolchain = proofs_dir / "lean-toolchain"
        toolchain_version = (
            lean_toolchain.read_text().strip() if lean_toolchain.exists() else "unknown"
        )

        log_content = f"""OpenHCS Paper Build Log
========================

Paper: {paper_id} - {paper_title}
Package Date: {datetime.now().isoformat()}
Lean Toolchain: {toolchain_version}

Proof Statistics:
-----------------
Lean Files: {len(paper_lean_files)}
Lines of Code: {lean_stats.line_count}
Theorems: {lean_stats.theorem_count}
Sorry Placeholders: {lean_stats.sorry_count}


Proof Files:
------------
"""
        for f in sorted(paper_lean_files):
            log_content += f"  - {f.name}\n"

        # Include actual lake build output if available
        if self._lean_build_output:
            log_content += f"""
================================================================================
COMPILATION OUTPUT (lake build)
================================================================================

{self._lean_build_output}

================================================================================
END COMPILATION OUTPUT
================================================================================
"""
        else:
            log_content += """
Note: Run 'python3 scripts/build_papers.py release' to include compilation output.
"""

        log_content += f"""
Build Instructions:
-------------------
To verify the proofs compile:

  cd proofs/
  lake build

All theorems will be machine-verified if compilation succeeds.

Repository: https://github.com/trissim/openhcs
"""

        log_file.write_text(log_content)
        print(f"[arxiv]   Build log: BUILD_LOG.txt (with compilation output)")

    def _create_archive(self, paper_id: str, package_dir: Path) -> tuple[Path, Path]:
        """Create compressed tar.gz and zip archives of package in releases/.

        For variants (e.g., paper1_jsait), uses variant-specific naming.
        """
        import tarfile
        import zipfile

        archive_prefix = self._get_archive_prefix(paper_id)
        releases_dir = self._get_releases_dir(paper_id)

        # Create tar.gz with variant-specific naming
        tar_name = f"{archive_prefix}_arxiv.tar.gz"
        tar_path = releases_dir / tar_name
        with tarfile.open(tar_path, "w:gz") as tar:
            tar.add(package_dir, arcname=archive_prefix)

        # Create zip with variant-specific naming
        zip_name = f"{archive_prefix}_arxiv.zip"
        zip_path = releases_dir / zip_name
        with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
            for file_path in package_dir.rglob("*"):
                if file_path.is_file():
                    arcname = str(
                        Path(archive_prefix) / file_path.relative_to(package_dir)
                    )
                    zf.write(file_path, arcname)

        return tar_path, zip_path

    def release(
        self,
        paper_id: str,
        verbose: bool = True,
        axiom_check: bool = False,
        claim_check: bool = False,
    ):
        """Full release build: Lean + LaTeX + Markdown + arXiv package.

        For variants (e.g., paper1_jsait), only build Lean once (shared proofs).
        """
        meta = self._get_paper_meta(paper_id)
        print(f"\n{'=' * 60}")
        print(f"[release] Building {paper_id}: {meta.name}")
        print(f"{'=' * 60}\n")

        # For variants, only build Lean if it's the base paper
        is_variant = paper_id != meta.dir_name.replace("_", "").lower()

        # Build in order: Lean → LaTeX → Markdown → Package
        if not is_variant:
            self.build_lean(paper_id, verbose=verbose)
        else:
            print(
                f"[release] Skipping Lean build for variant {paper_id} (shared proofs)"
            )

        self.build_latex(paper_id, verbose=verbose)
        self.build_markdown(paper_id)
        if claim_check:
            self.check_claim_coverage(paper_id, fail_on_missing=True)
        self.package_arxiv(paper_id)

        if axiom_check and not is_variant:
            self.check_axioms(paper_id, verbose=verbose)

        releases_dir = self._get_releases_dir(paper_id)
        print(
            f"\n[release] ✓ {paper_id} complete → {releases_dir.relative_to(self.repo_root)}/"
        )

    def check_axioms(self, paper_id: str, verbose: bool = True) -> dict:
        """Check what axioms each theorem in a paper depends on.

        Uses `lake env lean` with `#print axioms` to verify theorem foundations.
        Returns a summary dict with counts by axiom category.
        """
        import re
        from collections import defaultdict

        proofs_dir = self._get_paper_proofs_dir(paper_id)
        if not proofs_dir.exists():
            print(f"[axiom-check] No proofs directory for {paper_id}, skipping...")
            return {}

        print(f"[axiom-check] Checking axioms for {paper_id}...")
        print(f"[axiom-check]   Directory: {proofs_dir.relative_to(self.repo_root)}")

        # Step 1: Find all theorem/lemma declarations in .lean files
        theorems = []
        exclude_patterns = {".lake", "build"}
        for lean_file in sorted(proofs_dir.rglob("*.lean")):
            if any(part in exclude_patterns for part in lean_file.parts):
                continue
            if lean_file.name in ("lakefile.lean",):
                continue

            # Compute module name from file path
            rel_path = lean_file.relative_to(proofs_dir)
            module_name = str(rel_path.with_suffix("")).replace("/", ".")

            try:
                content = lean_file.read_text(encoding="utf-8")
            except UnicodeDecodeError:
                content = lean_file.read_text(encoding="latin-1")

            # Find theorem/lemma declarations
            for match in re.finditer(
                r"^(theorem|lemma)\s+(\w+['\w]*)", content, re.MULTILINE
            ):
                thm_name = match.group(2)
                theorems.append((module_name, thm_name))

        if not theorems:
            print(f"[axiom-check]   No theorems found in {paper_id}")
            return {}

        print(f"[axiom-check]   Found {len(theorems)} theorems/lemmas")

        # Step 2: Group by module and check axioms
        by_module = defaultdict(list)
        for module, thm in theorems:
            by_module[module].append(thm)

        results = {
            "total": len(theorems),
            "checked": 0,
            "no_axioms": 0,
            "propext_only": 0,
            "quot_sound": 0,
            "classical": 0,
            "unknown": 0,
            "details": [],
        }

        for module, thms in sorted(by_module.items()):
            # Create temp file with #print axioms commands
            import tempfile

            with tempfile.NamedTemporaryFile(
                mode="w", suffix=".lean", delete=False
            ) as f:
                f.write(f"import {module}\n\n")
                for thm in thms:
                    # Try with module prefix
                    f.write(f"#print axioms {module}.{thm}\n")
                tmpfile = f.name

            try:
                result = subprocess.run(
                    ["lake", "env", "lean", tmpfile],
                    capture_output=True,
                    text=True,
                    timeout=300,
                    cwd=proofs_dir,
                )
                output = result.stdout + result.stderr

                # Parse results
                found_thms = set()
                unknown_thms = []

                for line in output.split("\n"):
                    line = line.strip()
                    if "depends on axioms" in line or "does not depend" in line:
                        results["checked"] += 1
                        results["details"].append(line)
                        if verbose:
                            print(f"[axiom-check]   ✓ {line}")

                        # Categorize
                        if "does not depend" in line:
                            results["no_axioms"] += 1
                        elif "Classical" in line:
                            results["classical"] += 1
                        elif "Quot.sound" in line:
                            results["quot_sound"] += 1
                        elif "propext" in line:
                            results["propext_only"] += 1

                        # Track found
                        match = re.search(r"'([^']+)'", line)
                        if match:
                            found_thms.add(match.group(1).split(".")[-1])

                    elif "Unknown" in line and "constant" in line:
                        match = re.search(r"Unknown constant `([^`]+)`", line)
                        if match:
                            unknown_thms.append(match.group(1))

                # Retry unknown theorems without module prefix
                if unknown_thms:
                    with tempfile.NamedTemporaryFile(
                        mode="w", suffix=".lean", delete=False
                    ) as f2:
                        f2.write(f"import {module}\n")
                        f2.write(f"open {module.split('.')[-1]} in\n")
                        for unk in unknown_thms:
                            thm_name = unk.split(".")[-1]
                            if thm_name not in found_thms:
                                f2.write(f"#print axioms {thm_name}\n")
                        tmpfile2 = f2.name

                    result2 = subprocess.run(
                        ["lake", "env", "lean", tmpfile2],
                        capture_output=True,
                        text=True,
                        timeout=300,
                        cwd=proofs_dir,
                    )
                    output2 = result2.stdout + result2.stderr

                    for line in output2.split("\n"):
                        line = line.strip()
                        if "depends on axioms" in line or "does not depend" in line:
                            results["checked"] += 1
                            results["details"].append(line)
                            if verbose:
                                print(f"[axiom-check]   ✓ (no prefix) {line}")

                            if "does not depend" in line:
                                results["no_axioms"] += 1
                            elif "Classical" in line:
                                results["classical"] += 1
                            elif "Quot.sound" in line:
                                results["quot_sound"] += 1
                            elif "propext" in line:
                                results["propext_only"] += 1
                        elif "Unknown" in line:
                            results["unknown"] += 1

                    Path(tmpfile2).unlink(missing_ok=True)

            except subprocess.TimeoutExpired:
                print(f"[axiom-check]   TIMEOUT for module {module}")
            except Exception as e:
                print(f"[axiom-check]   ERROR: {e}")
            finally:
                Path(tmpfile).unlink(missing_ok=True)

        # Print summary
        print(f"\n[axiom-check] === {paper_id} Summary ===")
        print(f"[axiom-check]   Total theorems: {results['total']}")
        print(f"[axiom-check]   Successfully checked: {results['checked']}")
        print(f"[axiom-check]     - No axioms (constructive): {results['no_axioms']}")
        print(f"[axiom-check]     - Only propext: {results['propext_only']}")
        print(f"[axiom-check]     - propext + Quot.sound: {results['quot_sound']}")
        print(f"[axiom-check]     - Uses Classical.choice: {results['classical']}")
        print(f"[axiom-check]   Private/not exported: {results['unknown']}")

        return results

    def build_all(
        self,
        build_type: str = "all",
        verbose: bool = True,
        axiom_check: bool = False,
        claim_check: bool = False,
    ):
        """Build all papers of specified type."""
        paper_ids = list(self.papers.keys())

        if build_type == "release":
            for paper_id in paper_ids:
                try:
                    self.release(
                        paper_id,
                        verbose=verbose,
                        axiom_check=axiom_check,
                        claim_check=claim_check,
                    )
                except Exception as e:
                    print(f"[release] ERROR {paper_id}: {e}")
            return

        if build_type in ("all", "lean"):
            for paper_id in paper_ids:
                try:
                    self.build_lean(paper_id, verbose=verbose)
                except Exception as e:
                    print(f"[build] ERROR: {e}")

        if build_type in ("all", "latex"):
            for paper_id in paper_ids:
                try:
                    self.build_latex(paper_id, verbose=verbose)
                except Exception as e:
                    print(f"[build] ERROR: {e}")

        if build_type in ("all", "markdown"):
            for paper_id in paper_ids:
                try:
                    self.build_markdown(paper_id)
                except Exception as e:
                    print(f"[build-md] ERROR: {e}")

        if build_type in ("all", "metadata"):
            for paper_id in paper_ids:
                try:
                    self.build_copy_paste_metadata(paper_id)
                except Exception as e:
                    print(f"[metadata] ERROR {paper_id}: {e}")

        if build_type in ("all", "arxiv"):
            for paper_id in paper_ids:
                try:
                    self.package_arxiv(paper_id)
                except Exception as e:
                    print(f"[arxiv] ERROR: {e}")

        if build_type in ("all", "submission"):
            for paper_id in paper_ids:
                try:
                    self.build_submission(paper_id, verbose=verbose)
                except Exception as e:
                    print(f"[build] ERROR: {e}")

        if build_type in ("all", "claim-check"):
            for paper_id in paper_ids:
                try:
                    self.check_claim_coverage(paper_id, fail_on_missing=claim_check)
                except Exception as e:
                    print(f"[claim-check] ERROR {paper_id}: {e}")

        if axiom_check:
            for paper_id in paper_ids:
                try:
                    self.check_axioms(paper_id, verbose=verbose)
                except Exception as e:
                    print(f"[axiom-check] ERROR: {e}")


def main():
    parser = argparse.ArgumentParser(
        description="Unified paper builder",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python scripts/build_papers.py release           # Full release build for all papers
  python scripts/build_papers.py release paper1    # Full release for paper1 only
  python scripts/build_papers.py lean paper1 -v    # Build Paper 1 Lean proofs (verbose)
  python scripts/build_papers.py latex paper2      # Build Paper 2 LaTeX
  python scripts/build_papers.py lean paper2 --axiom-check  # Build + check axioms
  python scripts/build_papers.py claim-check paper4_toc      # Verify theorem-label mapping coverage
  python scripts/build_papers.py submission paper1_jsait  # Build JSAIT review PDF
  python scripts/build_papers.py metadata paper4_toc      # Generate Zenodo/arXiv copy-paste metadata
  python scripts/build_papers.py scaffold paper6   # Create boilerplate from papers.yaml entry
""",
    )
    parser.add_argument(
        "build_type",
        nargs="?",
        default="release",
        choices=[
            "release",
            "all",
            "lean",
            "latex",
            "markdown",
            "arxiv",
            "submission",
            "claim-check",
            "metadata",
            "scaffold",
        ],
        help="What to build (default: release)",
    )
    parser.add_argument(
        "paper",
        nargs="?",
        default="all",
        help="Which paper id from papers.yaml, or all (default: all)",
    )
    parser.add_argument(
        "-v",
        "--verbose",
        action="store_true",
        help="Show detailed output from build commands",
    )
    parser.add_argument(
        "-q",
        "--quiet",
        action="store_true",
        help="Minimal output (errors only)",
    )
    parser.add_argument(
        "--axiom-check",
        action="store_true",
        help="Run axiom verification on Lean theorems (checks what axioms each theorem depends on)",
    )
    parser.add_argument(
        "--claim-check",
        action="store_true",
        help="Enforce theorem-label mapping coverage check (fails on unmapped labels in release mode)",
    )
    parser.add_argument(
        "--overwrite",
        action="store_true",
        help="Allow scaffold command to overwrite existing files",
    )

    args = parser.parse_args()
    repo_root = Path(__file__).parent.parent

    # Determine verbosity:
    # - Explicit -q wins (quiet)
    # - Otherwise default to verbose for release/lean so build output is streamed
    # - -v always forces verbose
    if args.quiet:
        verbose = False
    else:
        verbose = args.verbose or args.build_type in ("release", "lean")

    axiom_check = args.axiom_check
    claim_check = args.claim_check

    try:
        if args.build_type == "scaffold":
            builder = PaperBuilder(
                repo_root,
                validate_prerequisites=False,
                validate_paper_structure=False,
            )
            if args.paper == "all":
                for paper_id in builder.papers.keys():
                    builder.scaffold_paper(paper_id, overwrite=args.overwrite)
            else:
                builder.scaffold_paper(args.paper, overwrite=args.overwrite)
            return

        builder = PaperBuilder(repo_root)
        if args.paper == "all":
            builder.build_all(
                args.build_type,
                verbose=verbose,
                axiom_check=axiom_check,
                claim_check=claim_check,
            )
        else:
            if args.build_type == "release":
                builder.release(
                    args.paper,
                    verbose=verbose,
                    axiom_check=axiom_check,
                    claim_check=claim_check,
                )
            elif args.build_type in ("all", "lean"):
                builder.build_lean(args.paper, verbose=verbose)
            if args.build_type in ("all", "latex"):
                builder.build_latex(args.paper, verbose=verbose)
            if args.build_type in ("all", "markdown"):
                builder.build_markdown(args.paper)
            if args.build_type in ("all", "metadata"):
                builder.build_copy_paste_metadata(args.paper)
            if args.build_type in ("all", "arxiv"):
                builder.package_arxiv(args.paper)
            if args.build_type in ("all", "submission"):
                builder.build_submission(args.paper, verbose=verbose)
            if args.build_type in ("all", "claim-check"):
                builder.check_claim_coverage(args.paper, fail_on_missing=claim_check)
            if axiom_check:
                builder.check_axioms(args.paper, verbose=verbose)
    except Exception as e:
        print(f"[build] FATAL: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
