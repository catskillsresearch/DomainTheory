#!/usr/bin/env python3
"""Flatten the DomainTheory.md note tree into arxiv.md, then build arxiv.tex / arxiv.pdf.

Walks markdown links from a root note (default ``DomainTheory.md``), expands
``@import`` directives relative to each note, writes a single ``arxiv.md``, and
optionally runs the existing TeX/PDF pipeline.

Lean imports default to path citations (the tree has ~2500 Lean modules). Pass
``--lean=inline`` to embed source listings.

Examples::

    python3 scripts/compile_md_tree.py                 # flatten + tex + pdf
    python3 scripts/compile_md_tree.py --md-only       # write arxiv.md only
    python3 scripts/compile_md_tree.py --lean=inline   # embed Lean listings
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = Path(__file__).resolve().parent
DEFAULT_ROOT_MD = ROOT / "DomainTheory.md"
ARXIV_MD = ROOT / "arxiv.md"

MD_LINK_RE = re.compile(r"\[([^\]]*)\]\(([^)]+\.md)\)")
# Bullet list item whose only content is a markdown link (TOC entry).
TOC_BULLET_RE = re.compile(
    r"^[ \t]*[-*][ \t]+\[([^\]]*)\]\(([^)]+\.md)\)[ \t]*$",
    re.MULTILINE,
)
IMPORT_RE = re.compile(
    r'^@import[ \t]+"([^"]+)"(?:[ \t]*\{([^}]*)\})?[ \t]*$',
    re.MULTILINE,
)
HEADING_RE = re.compile(r"^(#{1,6})[ \t]+(.+)$", re.MULTILINE)

DEFAULT_ABSTRACT = """\
This document is a machine-checked Lean 4 formalization of Dana Scott's papers
on domain theory: continuous lattices (1972), datatypes as lattices (1976),
neighbourhood systems (1980), and information systems (1982), together with
bridge theorems relating the three presentations. Each note in the source tree
is included in reading order from `DomainTheory.md`.
"""


ORPHAN_TEX_LINE = re.compile(
    r"^(?:"
    r"\\(?:bigcap|bigcup|sum|prod|int|frac|left|right|big|Big|mathcal|mathfrak|mathbb|text)"
    r"|=\s*\\left"
    # Short formula lines like `X \subseteq Y \quad \text{iff} ...` (not prose).
    r"|[A-Za-z][A-Za-z0-9_]*\s*(?:=|\\(?:subseteq|supseteq|in|notin|mid|cup|cap))\b"
    r")"
)
_PROSE_WORDS = re.compile(
    r"\b(?:the|and|that|with|this|from|which|have|been|also|within|domain|model)\b",
    re.IGNORECASE,
)


def repair_broken_display_math(text: str) -> str:
    """Move headings that were mistakenly placed inside ``$$...$$`` blocks out.

    Some notes open a display fence, then a ``##`` clause heading, then the
    formula and the closing fence. Pandoc then emits literal ``\\$\\$`` and raw
    TeX. Also drop empty orphan opening fences.
    """
    lines = text.splitlines(keepends=True)
    out: list[str] = []
    i = 0
    in_code = False
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        if stripped.startswith("```"):
            in_code = not in_code
            out.append(line)
            i += 1
            continue
        if in_code or stripped != "$$":
            out.append(line)
            i += 1
            continue
        # Potential display open: scan forward for close / heading.
        j = i + 1
        heading_idx: int | None = None
        close_idx: int | None = None
        while j < len(lines):
            s = lines[j].strip()
            if s.startswith("```"):
                break
            if s == "$$":
                close_idx = j
                break
            if s.startswith("#") and heading_idx is None:
                heading_idx = j
            j += 1
        if close_idx is None:
            # Orphan open: skip it.
            i += 1
            continue
        body_lines = lines[i + 1 : close_idx]
        if heading_idx is not None:
            headings: list[str] = []
            rest: list[str] = []
            seen_math = False
            for bl in body_lines:
                s = bl.strip()
                if not seen_math and s.startswith("#"):
                    headings.append(bl if bl.endswith("\n") else bl + "\n")
                elif not seen_math and not s:
                    continue
                else:
                    seen_math = True
                    rest.append(bl.rstrip("\n"))
            out.extend(headings)
            math = "\n".join(rest).strip("\n")
            if math.strip():
                out.append("$$\n" + math + "\n$$\n")
            i = close_idx + 1
            continue
        # Intact block: keep as-is (open + body + close).
        out.extend(lines[i : close_idx + 1])
        i = close_idx + 1
    return "".join(out)


def wrap_orphan_tex_display(text: str) -> str:
    """Wrap contiguous bare TeX math lines in ``$$...$$`` when not already fenced."""
    lines = text.splitlines(keepends=True)
    out: list[str] = []
    i = 0
    in_code = False
    in_math = False
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        if stripped.startswith("```"):
            in_code = not in_code
            out.append(line)
            i += 1
            continue
        # Toggle display-math fence; leave the line alone.
        if not in_code and stripped == "$$":
            in_math = not in_math
            out.append(line)
            i += 1
            continue
        if (
            not in_code
            and not in_math
            and stripped
            and ORPHAN_TEX_LINE.match(stripped)
            and not _PROSE_WORDS.search(stripped)
            and len(stripped) < 200
        ):
            chunk = [stripped]
            i += 1
            while i < len(lines):
                nxt = lines[i].strip()
                if not nxt or nxt.startswith("#") or nxt.startswith("```"):
                    break
                if nxt == "$$":
                    # Closing fence belonging to a half-broken block: consume it.
                    i += 1
                    break
                chunk.append(nxt)
                i += 1
            out.append("$$\n" + "\n".join(chunk) + "\n$$\n")
            continue
        out.append(line)
        i += 1
    return "".join(out)


def demote_headings(text: str, by: int) -> str:
    if by <= 0:
        return text

    def repl(m: re.Match[str]) -> str:
        level = len(m.group(1))
        new_level = min(level + by, 6)
        return "#" * new_level + " " + m.group(2)

    return HEADING_RE.sub(repl, text)


# AI-generated prose sidecars often contain raw TeX math macros outside math
# mode; omit them from the PDF by default (human English + Lean links remain).
AI_PROSE_SUFFIXES = {".ai_lean_to_english", ".ai_english_concordance"}


def expand_import(
    md_path: Path, rel: str, opts: str, *, lean_mode: str, include_ai_prose: bool
) -> str:
    target = (md_path.parent / rel).resolve()
    code_block = "code_block=false" not in (opts or "").replace(" ", "")
    suffix = target.suffix.lower()

    if not target.is_file():
        return f"\n\n*Missing import:* `{rel}`\n\n"

    if suffix == ".mermaid":
        body = target.read_text(encoding="utf-8").rstrip() + "\n"
        return f"\n\n```mermaid\n{body}```\n\n"

    if suffix == ".lean":
        try:
            rel_repo = target.relative_to(ROOT).as_posix()
        except ValueError:
            rel_repo = target.name
        if lean_mode == "omit":
            return "\n\n"
        if lean_mode == "link":
            return f"\n\n*Lean source:* [`{rel_repo}`]({rel_repo})\n\n"
        source = target.read_text(encoding="utf-8").rstrip() + "\n"
        return f"\n\n### {rel_repo}\n\n```lean\n{source}```\n\n"

    if suffix in AI_PROSE_SUFFIXES and not include_ai_prose:
        return "\n\n"

    # Prose sidecars (.english, optionally AI English, …)
    text = target.read_text(encoding="utf-8").rstrip() + "\n"
    if not code_block or suffix == ".english" or suffix in AI_PROSE_SUFFIXES:
        return f"\n\n{text}\n"
    lang = suffix.lstrip(".") or "text"
    return f"\n\n```{lang}\n{text}```\n\n"


def expand_imports(
    md_path: Path, text: str, *, lean_mode: str, include_ai_prose: bool
) -> str:
    def repl(m: re.Match[str]) -> str:
        return expand_import(
            md_path,
            m.group(1),
            m.group(2) or "",
            lean_mode=lean_mode,
            include_ai_prose=include_ai_prose,
        )

    return IMPORT_RE.sub(repl, text)


def child_md_targets(md_path: Path, text: str) -> list[tuple[str, Path]]:
    """TOC children in document order (first occurrence of each path)."""
    seen: set[Path] = set()
    out: list[tuple[str, Path]] = []
    for title, href in TOC_BULLET_RE.findall(text):
        tgt = (md_path.parent / href).resolve()
        if tgt in seen or not tgt.is_file():
            continue
        seen.add(tgt)
        out.append((title, tgt))
    return out


def strip_toc_bullets(text: str) -> str:
    return TOC_BULLET_RE.sub("", text)


def flatten_file(
    md_path: Path,
    *,
    depth: int,
    lean_mode: str,
    include_ai_prose: bool,
    visited: set[Path],
) -> str:
    """Recursively flatten one note and its TOC-linked children."""
    resolved = md_path.resolve()
    if resolved in visited:
        return f"\n\n*(Already included: `{md_path.name}`.)*\n\n"
    visited.add(resolved)

    raw = resolved.read_text(encoding="utf-8")
    children = child_md_targets(resolved, raw)
    body = strip_toc_bullets(raw) if children else raw
    body = expand_imports(
        resolved, body, lean_mode=lean_mode, include_ai_prose=include_ai_prose
    )
    # Cap demotion at 2 so leaf `# Title` becomes `###` (not `####`, which the
    # TeX pipeline may flatten to bold inventory rows).
    body = demote_headings(body, min(depth, 2))
    # Repair `$$` / heading inversions, then wrap remaining bare TeX displays.
    body = repair_broken_display_math(body)
    body = wrap_orphan_tex_display(body)
    # Collapse excess blank lines left by stripped TOC bullets / omitted AI prose.
    body = re.sub(r"\n{3,}", "\n\n", body).strip() + "\n"

    parts = [body]
    for _title, child in children:
        parts.append(
            flatten_file(
                child,
                depth=depth + 1,
                lean_mode=lean_mode,
                include_ai_prose=include_ai_prose,
                visited=visited,
            )
        )
    return "\n".join(parts)


def ensure_abstract(text: str) -> str:
    if re.search(r"^##\s+Abstract\s*$", text, re.MULTILINE):
        return text
    # Insert after the first top-level title line.
    m = re.match(r"^#\s+.+\n+", text)
    if not m:
        return "## Abstract\n\n" + DEFAULT_ABSTRACT + "\n\n" + text
    insert_at = m.end()
    return (
        text[:insert_at]
        + "## Abstract\n\n"
        + DEFAULT_ABSTRACT
        + "\n\n"
        + text[insert_at:]
    )


def ensure_model_card_markers(text: str) -> str:
    """Ensure References has AI model-card placeholders expected by ``ai_model_cards``."""
    if "<!-- AI_MODEL_REFERENCES -->" in text:
        return text
    m = re.search(r"^(#{1,6}\s+References)\s*$", text, re.MULTILINE)
    if not m:
        text = text.rstrip() + "\n\n## References\n\n"
        m = re.search(r"^(#{1,6}\s+References)\s*$", text, re.MULTILINE)
        assert m is not None
    insert_at = m.end()
    return (
        text[:insert_at]
        + "\n\n<!-- AI_MODEL_REFERENCES -->\n<!-- /AI_MODEL_REFERENCES -->\n"
        + text[insert_at:]
    )


def flatten_md_tree(
    root_md: Path = DEFAULT_ROOT_MD,
    *,
    lean_mode: str = "link",
    include_ai_prose: bool = False,
    out_path: Path = ARXIV_MD,
) -> Path:
    """Compile the markdown tree rooted at ``root_md`` into ``out_path``."""
    if not root_md.is_file():
        raise FileNotFoundError(f"missing root markdown: {root_md}")
    if lean_mode not in {"link", "inline", "omit"}:
        raise ValueError(f"unknown lean_mode: {lean_mode!r}")

    visited: set[Path] = set()
    body = flatten_file(
        root_md,
        depth=0,
        lean_mode=lean_mode,
        include_ai_prose=include_ai_prose,
        visited=visited,
    )
    body = ensure_abstract(body)
    body = ensure_model_card_markers(body)
    header = (
        "<!-- AUTO-GENERATED by scripts/compile_md_tree.py — do not edit -->\n"
        f"<!-- Root: {root_md.relative_to(ROOT).as_posix()} "
        f"({len(visited)} notes, lean={lean_mode}, "
        f"ai_prose={'on' if include_ai_prose else 'off'}) -->\n\n"
    )
    out_path.write_text(header + body, encoding="utf-8")
    return out_path


def build_arxiv_with_code() -> None:
    subprocess.run(
        [sys.executable, str(SCRIPTS / "generate_arxiv_with_code.py")],
        cwd=ROOT,
        check=True,
    )


def build_arxiv_tex() -> None:
    subprocess.run(
        [sys.executable, str(SCRIPTS / "build_arxiv_tex.py")],
        cwd=ROOT,
        check=True,
    )


def build_arxiv_pdf(*, clean: bool = False) -> None:
    tex = ROOT / "arxiv.tex"
    if not tex.is_file():
        raise FileNotFoundError("missing arxiv.tex; build TeX first")
    if clean:
        subprocess.run(["latexmk", "-C", "arxiv.tex"], cwd=ROOT, check=False)
    proc = subprocess.run(
        ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error", "arxiv.tex"],
        cwd=ROOT,
        check=False,
    )
    if proc.returncode != 0:
        log = ROOT / "arxiv.log"
        if log.is_file():
            sys.stderr.write(log.read_text(encoding="utf-8", errors="replace")[-4000:])
        raise RuntimeError("latexmk failed compiling arxiv.tex")
    pdf = ROOT / "arxiv.pdf"
    if not pdf.is_file():
        raise RuntimeError("arxiv.pdf missing after latexmk")


def compile_tree_to_pdf(
    root_md: Path = DEFAULT_ROOT_MD,
    *,
    lean_mode: str = "link",
    include_ai_prose: bool = False,
    md_only: bool = False,
    tex_only: bool = False,
    clean: bool = False,
) -> Path:
    """Flatten the note tree and build ``arxiv.pdf`` (unless ``md_only`` / ``tex_only``)."""
    out = flatten_md_tree(
        root_md, lean_mode=lean_mode, include_ai_prose=include_ai_prose
    )
    print(f"wrote {out.relative_to(ROOT)} ({out.stat().st_size:,} bytes)")
    if md_only:
        return out
    build_arxiv_with_code()
    build_arxiv_tex()
    if tex_only:
        return ROOT / "arxiv.tex"
    build_arxiv_pdf(clean=clean)
    pdf = ROOT / "arxiv.pdf"
    print(f"wrote {pdf.relative_to(ROOT)} ({pdf.stat().st_size:,} bytes)")
    return pdf


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=DEFAULT_ROOT_MD,
        help="root markdown file (default: DomainTheory.md)",
    )
    parser.add_argument(
        "--lean",
        choices=("link", "inline", "omit"),
        default="link",
        help="how to expand @import of .lean files (default: link)",
    )
    parser.add_argument(
        "--ai-prose",
        action="store_true",
        help="include .ai_lean_to_english / .ai_english_concordance imports",
    )
    parser.add_argument(
        "--md-only",
        action="store_true",
        help="only write arxiv.md",
    )
    parser.add_argument(
        "--tex-only",
        action="store_true",
        help="write arxiv.md and arxiv.tex, skip PDF",
    )
    parser.add_argument(
        "--clean",
        action="store_true",
        help="latexmk -C before compiling the PDF",
    )
    args = parser.parse_args(argv)
    root = args.root if args.root.is_absolute() else ROOT / args.root
    compile_tree_to_pdf(
        root,
        lean_mode=args.lean,
        include_ai_prose=args.ai_prose,
        md_only=args.md_only,
        tex_only=args.tex_only,
        clean=args.clean,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
