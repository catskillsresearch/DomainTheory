#!/usr/bin/env python3
"""Copy the notes under DomainTheory.md into build/, expanding Lean links.

build/arxiv.md is the entry note. Every other note keeps the path it has in
the repository, under build/. Markdown links are rewritten to start with
build/ so a preview opened at the repository root follows the expanded
copies. Each local Lean link is left in place and followed by a fenced copy of
that file. The copy omits `module`, imports, `public section`, and `open`
commands, and omits `/-!` Scott extracts. A leading `/-ai` comment is
shown above the code as a blockquote.
"""

from __future__ import annotations

import re
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ENTRY = ROOT / "DomainTheory.md"
BUILD = ROOT / "build"
LEGACY = ROOT / "arxiv.md"

LINK = re.compile(r"\[([^\]]*)\]\(([^)]+)\)")
FENCE = re.compile(r"^\s*(`{3,})")
IMPORT_LINE = re.compile(r"^(?:public\s+|private\s+|meta\s+)?import\b")
PUBLIC_SECTION = re.compile(r"^(?:@\[[^\]]*\]\s*)?public\s+section\s*$")
OPEN_LINE = re.compile(r"^open\b")


def resolve_link(base: Path, href: str, suffix: str) -> Path | None:
    href = href.strip()
    if href.startswith(("http://", "https://", "mailto:")):
        return None
    path = href.split("#", 1)[0]
    if not path.endswith(suffix):
        return None
    target = (base.parent / path).resolve()
    try:
        target.relative_to(ROOT)
    except ValueError:
        return None
    return target


def notes_from(note: Path, found: dict[Path, None]) -> None:
    if note in found or not note.is_file():
        return
    found[note] = None
    text = note.read_text(encoding="utf-8")
    in_fence = False
    for line in text.splitlines():
        fence = FENCE.match(line)
        if fence is not None:
            if not in_fence:
                in_fence = True
            elif line.lstrip().startswith(fence.group(1)):
                in_fence = False
            continue
        if in_fence:
            continue
        for match in LINK.finditer(line):
            target = resolve_link(note, match.group(2), ".md")
            if target is not None:
                notes_from(target, found)


def output_path(note: Path) -> Path:
    if note == ENTRY.resolve():
        return BUILD / "arxiv.md"
    return BUILD / note.relative_to(ROOT)


def fence_for(text: str) -> str:
    longest = 0
    run = 0
    for char in text:
        if char == "`":
            run += 1
            longest = max(longest, run)
        else:
            run = 0
    return "`" * max(4, longest + 1)


def take_block(text: str, start: int, opener: str, closer: str) -> tuple[str, int] | None:
    if not text.startswith(opener, start):
        return None
    end = text.find(closer, start + len(opener))
    if end < 0:
        return None
    body = text[start + len(opener) : end]
    return body, end + len(closer)


def split_preamble(text: str) -> tuple[str | None, str]:
    """Return the first `/-ai` comment and the source with that comment and every `/-!` block removed."""
    ai: str | None = None
    out: list[str] = []
    index = 0
    while index < len(text):
        if ai is None:
            taken = take_block(text, index, "/-ai", "ai-/")
            if taken is not None:
                ai = taken[0].strip()
                index = taken[1]
                continue
        taken = take_block(text, index, "/-!", "-/")
        if taken is not None:
            index = taken[1]
            continue
        out.append(text[index])
        index += 1
    return ai, "".join(out)


def elide_declarations(text: str) -> str:
    kept: list[str] = []
    blank = False
    for line in text.splitlines():
        stripped = line.strip()
        if (
            stripped == "module"
            or IMPORT_LINE.match(stripped)
            or PUBLIC_SECTION.match(stripped)
            or OPEN_LINE.match(stripped)
        ):
            continue
        if not stripped:
            if kept and not blank:
                kept.append("")
                blank = True
            continue
        kept.append(line.rstrip())
        blank = False
    return "\n".join(kept).strip()


def ai_box(comment: str) -> str:
    paragraphs = [part.strip() for part in re.split(r"\n\s*\n", comment) if part.strip()]
    lines: list[str] = []
    for index, paragraph in enumerate(paragraphs):
        if index:
            lines.append(">")
        for line in paragraph.splitlines():
            lines.append("> " + line.strip())
    return "\n".join(lines)


def lean_block(path: Path) -> str:
    if not path.is_file():
        raise FileNotFoundError(path)
    ai, source = split_preamble(path.read_text(encoding="utf-8"))
    code = elide_declarations(source)
    parts: list[str] = []
    if ai:
        parts.append(ai_box(ai))
    if code:
        if parts:
            parts.append("")
        body = code + "\n"
        fence = fence_for(body)
        parts.append(f"{fence}lean\n{body}{fence}")
    return "\n".join(parts)


def build_href(note: Path, href: str, notes: dict[Path, None]) -> str | None:
    target = resolve_link(note, href, ".md")
    if target is None or target not in notes:
        return None
    fragment = ""
    if "#" in href:
        fragment = href[href.index("#") :]
    if target == ENTRY.resolve():
        return f"build/arxiv.md{fragment}"
    return "build/" + target.relative_to(ROOT).as_posix() + fragment


def rewrite_note_links(note: Path, line: str, notes: dict[Path, None]) -> str:
    def replace(match: re.Match[str]) -> str:
        href = build_href(note, match.group(2), notes)
        if href is None:
            return match.group(0)
        return f"[{match.group(1)}]({href})"

    return LINK.sub(replace, line)


def lean_targets(note: Path, line: str) -> list[Path]:
    found: list[Path] = []
    for match in LINK.finditer(line):
        target = resolve_link(note, match.group(2), ".lean")
        if target is not None:
            found.append(target)
    return found


def expand(note: Path, notes: dict[Path, None]) -> tuple[str, int]:
    blocks = 0
    out: list[str] = []
    in_fence = False
    for line in note.read_text(encoding="utf-8").splitlines():
        fence = FENCE.match(line)
        if fence is not None:
            if not in_fence:
                in_fence = True
            elif line.lstrip().startswith(fence.group(1)):
                in_fence = False
            out.append(line)
            continue
        if in_fence:
            out.append(line)
            continue
        line = rewrite_note_links(note, line, notes)
        out.append(line)
        for lean in lean_targets(note, line):
            out.append("")
            out.append(lean_block(lean))
            out.append("")
            blocks += 1
    return "\n".join(out).rstrip() + "\n", blocks


def main() -> None:
    if not ENTRY.is_file():
        sys.exit(f"missing {ENTRY}")
    notes: dict[Path, None] = {}
    notes_from(ENTRY.resolve(), notes)
    if BUILD.exists():
        shutil.rmtree(BUILD)
    BUILD.mkdir(parents=True)
    if LEGACY.is_file():
        LEGACY.unlink()
    total_blocks = 0
    for note in notes:
        body, blocks = expand(note, notes)
        destination = output_path(note)
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(body, encoding="utf-8")
        total_blocks += blocks
    print(
        f"wrote {BUILD} ({len(notes)} notes, {total_blocks} Lean blocks; "
        f"entry {BUILD / 'arxiv.md'})"
    )


if __name__ == "__main__":
    main()
