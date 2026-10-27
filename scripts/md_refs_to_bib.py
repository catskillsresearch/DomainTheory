#!/usr/bin/env python3
"""Convert DomainTheory/References.md (+ model cards) into references.bib.

Preserves explicit cite keys (``**[Sco72]**`` etc.). Generates stable
author+year keys for unkeyed rows. Appends the three model-card entries from
``ai_model_cards.py``.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))

from ai_model_cards import MODEL_CARDS, render_model_bibtex  # noqa: E402

SRC = ROOT / "DomainTheory" / "References.md"
OUT = ROOT / "references.bib"

KEY_RE = re.compile(r"\s*\*\*\[([A-Za-z0-9]+)\]\*\*\s*$")
HEAD_RE = re.compile(
    r"^(?P<author>.+?)\s*\((?P<year>[^)]+)\)\s*,\s*(?P<rest>.*)$",
    re.DOTALL,
)


def strip_md(s: str) -> str:
    s = re.sub(r"<([^>]+)>", r"\\url{\1}", s)
    s = re.sub(r"`([^`]+)`", r"\\texttt{\1}", s)
    s = re.sub(r"\*\*([^*]+)\*\*", r"\1", s)
    s = re.sub(r"\*([^*]+)\*", r"\1", s)
    return s.strip().rstrip(".")


def make_key(author: str, year: str, explicit: str | None, used: set[str]) -> str:
    if explicit:
        return explicit
    a = re.sub(r"\bet al\.\b", "", author, flags=re.I)
    parts = re.split(r"\s+and\s+|,", a)[0].strip()
    tokens = re.findall(r"[A-Za-zÀ-ÿ]+", parts)
    surname = tokens[-1] if tokens else "Ref"
    ym = re.search(r"(\d{4})", year)
    if ym:
        y = ym.group(1)[2:]
    elif "to appear" in year.lower():
        y = "TA"
    else:
        y = re.sub(r"[^A-Za-z0-9]", "", year)[:4] or "XX"
    suf = ""
    sm = re.search(r"\d{4}([a-z])", year)
    if sm:
        suf = sm.group(1)
    base = re.sub(r"[^A-Za-z0-9]", "", f"{surname[:12]}{y}{suf}")
    key = base
    n = 2
    while key in used:
        key = f"{base}{n}"
        n += 1
    return key


def entry_block(key: str, author: str, year: str, rest: str) -> str:
    title = None
    how = rest
    im = re.match(r"\*([^*]+)\*\.?\s*(.*)$", rest, re.DOTALL)
    if im:
        title = im.group(1).strip()
        how = im.group(2).strip()
    else:
        sm = re.match(r"([^.]+\.)\s*(.*)$", rest, re.DOTALL)
        if sm:
            title = sm.group(1).rstrip(".").strip()
            how = sm.group(2).strip()
        else:
            title = rest
            how = ""

    title = strip_md(title)
    how = strip_md(how).lstrip(" ,;") if how else ""
    author_b = strip_md(author)
    ym = re.search(r"(\d{4})", year)
    year_field = ym.group(1) if ym else None

    lines = [f"@misc{{{key},"]
    lines.append(f"  author = {{{author_b}}},")
    lines.append(f"  title = {{{title}}},")
    if year_field:
        lines.append(f"  year = {{{year_field}}},")
    note_parts: list[str] = []
    if year_field is None or year != year_field:
        if not (year_field and year == year_field):
            if year != (year_field or ""):
                note_parts.append(year)
    if how:
        note_parts.append(how)
    # Drop redundant year-only note when it equals year_field
    note_parts = [p for p in note_parts if p and p != year_field]
    if note_parts:
        lines.append(f"  note = {{{'; '.join(note_parts)}}},")
    lines.append("}")
    return "\n".join(lines)


def main() -> int:
    if not SRC.is_file():
        print(f"error: missing {SRC}", file=sys.stderr)
        return 1
    raw = SRC.read_text(encoding="utf-8")
    body = re.sub(r"^#\s+References\s*\n+", "", raw)
    # If References.md was already stubbed, refuse to overwrite bib from stub.
    paras = [p.strip() for p in re.split(r"\n\s*\n", body) if p.strip()]
    if len(paras) < 10:
        print(
            f"error: {SRC} looks stubbed ({len(paras)} paragraphs); "
            "restore prose list before regenerating",
            file=sys.stderr,
        )
        return 1

    used: set[str] = {c.cite_key for c in MODEL_CARDS}
    blocks: list[str] = []
    for para in paras:
        mkey = KEY_RE.search(para)
        explicit = mkey.group(1) if mkey else None
        text = KEY_RE.sub("", para).strip()
        hm = HEAD_RE.match(text)
        if hm:
            author = hm.group("author").strip()
            year = hm.group("year").strip()
            rest = hm.group("rest").strip()
        else:
            author = "Unknown"
            year = "n.d."
            rest = text
        key = make_key(author, year, explicit, used)
        used.add(key)
        blocks.append(entry_block(key, author, year, rest))

    out_lines = [
        "% Auto-generated from DomainTheory/References.md + scripts/ai_model_cards.py",
        "% Regenerate with: python3 scripts/md_refs_to_bib.py",
        "",
        *sum(([b, ""] for b in blocks), []),
        "% --- AI model cards (this revision) ---",
        "",
        render_model_bibtex(),
        "",
    ]
    OUT.write_text("\n".join(out_lines), encoding="utf-8")
    print(f"wrote {OUT} ({len(blocks)} prose + {len(MODEL_CARDS)} model cards)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
