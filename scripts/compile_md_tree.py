#!/usr/bin/env python3
"""Flatten the DomainTheory.md note tree into arxiv.md, then build arxiv.tex / arxiv.pdf.

Walks markdown links from a root note (default ``DomainTheory.md``), expands
``@import`` directives relative to each note, writes a single ``arxiv.md``, and
optionally runs the existing TeX/PDF pipeline.

Outline structure follows TOC bullets (and numbered lists like ``1. [Section](…)``):
each link hop adds one markdown heading level so LaTeX numbering runs
1 → 1.1 → 1.1.1. Section titles come from the link text, not the linked file's
``#`` heading.

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
# Outline entry: bullet or numbered list item linking to another note.
TOC_BULLET_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?:[-*][ \t]+|\d+\.\s+)\[(?P<title>[^\]]*)\]\((?P<href>[^)]+\.md)\)[ \t]*$",
    re.MULTILINE,
)
FIRST_H1_RE = re.compile(r"^#\s+.+?(?:\n+|$)", re.MULTILINE)
IMPORT_RE = re.compile(
    r'^@import[ \t]+"([^"]+)"(?:[ \t]*\{([^}]*)\})?[ \t]*$',
    re.MULTILINE,
)
HEADING_RE = re.compile(r"^(#{1,6})[ \t]+(.+)$", re.MULTILINE)

DEFAULT_ABSTRACT = """\
This document is a machine-checked Lean 4 formalization of Dana Scott's papers
on domain theory: continuous lattices (1972), datatypes as lattices (1976),
neighbourhood systems (1980), and information systems (1982), together with
bridge theorems relating the lattice, neighbourhood, and information systems presentations.
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


def repair_cases_row_breaks(text: str) -> str:
    """Insert ``\\\\`` between ``cases`` rows when Scott source omitted the line break."""
    out: list[str] = []
    i = 0
    marker = "\\begin{cases}"
    end_marker = "\\end{cases}"
    while i < len(text):
        start = text.find(marker, i)
        if start == -1:
            out.append(text[i:])
            break
        out.append(text[i:start])
        end = text.find(end_marker, start)
        if end == -1:
            out.append(text[start:])
            break
        block = text[start : end + len(end_marker)]
        block = re.sub(
            r"([;,])\s+(\\(?:bot|perp|top|[A-Za-z{])) &",
            r"\1 \\\\ \2 &",
            block,
        )
        block = re.sub(
            r",(?!\s*\\\\)\s*\n(\s*)(?=[^\n]+&)",
            r", \\\\\n\1",
            block,
        )
        out.append(block)
        i = end + len(end_marker)
    return "".join(out)


def repair_array_row_breaks(text: str) -> str:
    """Insert ``\\\\`` between ``array`` rows when Scott source omitted them."""
    out: list[str] = []
    i = 0
    marker = "\\begin{array}"
    end_marker = "\\end{array}"
    while i < len(text):
        start = text.find(marker, i)
        if start == -1:
            out.append(text[i:])
            break
        out.append(text[i:start])
        end = text.find(end_marker, start)
        if end == -1:
            out.append(text[start:])
            break
        block = text[start : end + len(end_marker)]
        block = re.sub(
            r"(?<!\n)(?<!\$)(?<![\\])\n(\s*)([^\n\\]+&[^\n]*)\n(\s*)([^\n\\]+&)",
            r"\n\1\2 \\\\\n\3\4",
            block,
        )
        out.append(block)
        i = end + len(end_marker)
    return "".join(out)


_SET_COMP = re.compile(
    r"(?<![\\{])"
    r"(?:\\sqcap\s+)?"
    r"[A-Za-z0-9_'\\]+\s+\\in\s+[A-Za-z0-9_{}\\']+\s*:\s*"
    r"[^,;\n$]+?"
    r"(?=[,;.\\]|$|\s+will|\s+is|\s+are|\s+form|\s+remain|\s+can|\s+where|\s+for|\s+and|\s+or|\s+as|\s+—|\s+–|\s+-|\s+\\)",
)


def _wrap_set_comprehensions_in_math(body: str) -> str:
    if "\\{" in body and not _SET_COMP.search(body):
        return body

    def repl(m: re.Match[str]) -> str:
        inner = m.group(0).strip()
        if inner.startswith("{") or inner.startswith("\\{"):
            return m.group(0)
        return "{ " + inner + " }"

    return _SET_COMP.sub(repl, body)


def repair_bare_set_comprehensions(text: str) -> str:
    """Scott prose often writes ``$y \\in D : P$`` without set braces."""

    def fix_inline(m: re.Match[str]) -> str:
        return "$" + _wrap_set_comprehensions_in_math(m.group(1)) + "$"

    text = re.sub(r"(?<!\$)\$(?!\$)([^\n$]+?)(?<!\$)\$(?!\$)", fix_inline, text)

    def fix_display(m: re.Match[str]) -> str:
        return "$$" + _wrap_set_comprehensions_in_math(m.group(1)) + "$$"

    text = re.sub(r"\$\$([^\$]+?)\$\$", fix_display, text, flags=re.DOTALL)
    return text


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


def indent_columns(indent: str) -> int:
    return len(indent.expandtabs(4))


def shift_headings(text: str, delta: int) -> str:
    if delta == 0:
        return text

    def repl(m: re.Match[str]) -> str:
        level = len(m.group(1))
        new_level = min(max(level + delta, 1), 6)
        return "#" * new_level + " " + m.group(2)

    return HEADING_RE.sub(repl, text)


def align_body_headings(text: str, base_level: int) -> str:
    """Shift headings so the shallowest one in ``text`` is ``base_level``."""
    levels = [len(m.group(1)) for m in HEADING_RE.finditer(text)]
    if not levels:
        return text
    delta = base_level - min(levels)
    return shift_headings(text, delta)


def strip_first_h1(text: str) -> str:
    return FIRST_H1_RE.sub("", text, count=1)


# AI-generated prose sidecars often contain raw TeX math macros outside math
# mode; omit them from the PDF by default (human English + Lean links remain).
AI_PROSE_SUFFIXES = {".ai_lean_to_english", ".ai_english_concordance"}


BOLD_LEAN_CITATION_ABOVE = re.compile(
    r"\*\*\[[^\]]*\]\([^)]+\.lean\)\*\*\s*\n+\s*$"
)
BOLD_LEAN_CITATION_LINE = re.compile(
    r"^\s*\*\*\[[^\]]*\]\(([^)]+\.lean)\)\*\*\s*$",
    re.MULTILINE,
)


def resolve_lean_target(md_path: Path, href_or_rel: str) -> Path:
    s = href_or_rel.split("#", 1)[0].strip()
    if s.startswith("DomainTheory/"):
        return (ROOT / s).resolve()
    p = Path(s)
    if p.is_absolute():
        return p.resolve()
    return (md_path.parent / s).resolve()


def strip_duplicate_lean_citations(
    md_path: Path, text: str, included_lean: set[Path]
) -> str:
    """Drop repeated ``**[…](*.lean)**`` lines once that module is already in the PDF."""
    if not included_lean:
        return text

    def repl(m: re.Match[str]) -> str:
        target = resolve_lean_target(md_path, m.group(1))
        if target in included_lean:
            return ""
        return m.group(0)

    return BOLD_LEAN_CITATION_LINE.sub(repl, text)


def expand_import(
    md_path: Path,
    rel: str,
    opts: str,
    *,
    lean_mode: str,
    include_ai_prose: bool,
    cited_above: bool = False,
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
        source = target.read_text(encoding="utf-8").rstrip() + "\n"
        fenced = f"\n\n```lean\n{source}```\n\n"
        if lean_mode == "link":
            # Notes cite the file with ** [label](path) **; @import supplies the listing only.
            if cited_above:
                return fenced
            return f"\n\n**[{rel_repo}]({rel_repo})**\n\n{fenced.lstrip()}"
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
    md_path: Path,
    text: str,
    *,
    lean_mode: str,
    include_ai_prose: bool,
    included_lean: set[Path],
) -> str:
    text = strip_duplicate_lean_citations(md_path, text, included_lean)

    def repl(m: re.Match[str]) -> str:
        rel = m.group(1)
        target = resolve_lean_target(md_path, rel)
        if (
            target.suffix.lower() == ".lean"
            and lean_mode != "omit"
            and target in included_lean
        ):
            return ""
        before = text[max(0, m.start() - 500) : m.start()]
        cited_above = bool(BOLD_LEAN_CITATION_ABOVE.search(before))
        chunk = expand_import(
            md_path,
            rel,
            m.group(2) or "",
            lean_mode=lean_mode,
            include_ai_prose=include_ai_prose,
            cited_above=cited_above,
        )
        if target.suffix.lower() == ".lean" and lean_mode != "omit" and target.is_file():
            included_lean.add(target)
        return chunk

    return IMPORT_RE.sub(repl, text)


def child_md_targets(md_path: Path, text: str) -> list[tuple[int, str, Path]]:
    """TOC children in document order: ``(relative_indent, title, path)``."""
    matches = list(TOC_BULLET_RE.finditer(text))
    if not matches:
        return []
    base_indent = min(indent_columns(m.group("indent")) for m in matches)
    seen: set[Path] = set()
    out: list[tuple[int, str, Path]] = []
    for m in matches:
        rel = (indent_columns(m.group("indent")) - base_indent) // 2
        href = m.group("href")
        title = m.group("title").strip()
        tgt = (md_path.parent / href).resolve()
        if tgt in seen or not tgt.is_file():
            continue
        seen.add(tgt)
        out.append((rel, title, tgt))
    return out


def strip_toc_bullets(text: str) -> str:
    return TOC_BULLET_RE.sub("", text)


def flatten_file(
    md_path: Path,
    *,
    section_level: int,
    section_title: str | None,
    lean_mode: str,
    include_ai_prose: bool,
    visited: set[Path],
    included_lean: set[Path],
) -> str:
    """Recursively flatten one note and its TOC-linked children."""
    resolved = md_path.resolve()
    if resolved in visited:
        return f"\n\n*(Already included: `{md_path.name}`.)*\n\n"
    visited.add(resolved)

    section_level = min(max(section_level, 1), 6)

    raw = resolved.read_text(encoding="utf-8")
    children = child_md_targets(resolved, raw)
    body = strip_toc_bullets(raw) if children else raw
    if section_title is not None:
        body = strip_first_h1(body)
    body = expand_imports(
        resolved,
        body,
        lean_mode=lean_mode,
        include_ai_prose=include_ai_prose,
        included_lean=included_lean,
    )
    if section_title is not None:
        body = align_body_headings(body, min(section_level + 1, 6))
    body = repair_cases_row_breaks(body)
    body = repair_array_row_breaks(body)
    body = repair_bare_set_comprehensions(body)
    # Repair `$$` / heading inversions, then wrap remaining bare TeX displays.
    body = repair_broken_display_math(body)
    body = wrap_orphan_tex_display(body)
    body = re.sub(r"\n{3,}", "\n\n", body).strip() + "\n"

    parts: list[str] = []
    if section_title is not None:
        parts.append(f"{'#' * section_level} {section_title}\n\n{body}")
    else:
        parts.append(body)

    for rel_indent, title, child in children:
        # One outline link = one deeper section (1 → 1.1 → 1.1.1); indent nests further.
        child_level = min(section_level + 1 + rel_indent, 6)
        parts.append(
            flatten_file(
                child,
                section_level=child_level,
                section_title=title,
                lean_mode=lean_mode,
                include_ai_prose=include_ai_prose,
                visited=visited,
                included_lean=included_lean,
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
    included_lean: set[Path] = set()
    body = flatten_file(
        root_md,
        section_level=1,
        section_title=None,
        lean_mode=lean_mode,
        include_ai_prose=include_ai_prose,
        visited=visited,
        included_lean=included_lean,
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


def refresh_note_lean_imports() -> None:
    """Retarget broken Lean ``@import``s in notes before flattening (Pref folds, etc.)."""
    from refresh_note_lean_imports import refresh_all

    print("==> Refreshing Lean @imports in notes")
    n = refresh_all(ROOT / "DomainTheory")
    print(f"updated {n} notes")


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
    refresh_note_lean_imports()
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
