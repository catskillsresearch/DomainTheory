#!/usr/bin/env python3
"""Migrate DomainTheory notes to the four-section MPE template."""

from __future__ import annotations

import argparse
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DT = ROOT / "DomainTheory"

# Reference note — already in the target four-section layout.
SKIP_MD: frozenset[Path] = frozenset(
    {
        DT / "ContinuousLattice/Constructions/1972_Proposition_2_9.md",
    }
)

LEAN_SECTION = re.compile(r"^\*\*Lean", re.M)
TITLE = re.compile(r"^(# .+)\n", re.M)
BULLET_LEAN = re.compile(r"^\s*-\s+\[([^\]]*)\]\(([^)]+\.lean)\)\s*$", re.M)
IMPORT_LEAN = re.compile(r'^@import\s+"([^"]+\.lean)"', re.M)
ALREADY_MIGRATED = re.compile(r"^## Human-English\s*$", re.M)

TOP_LEVEL_LEAN = re.compile(
    r"(?:^|/)(Exercise\d+[a-zA-Z0-9]*|effectiveIso[^/]+|theorem_[^/]+|proposition_[^/]+|"
    r"lemma_[^/]+|corollary_[^/]+|definition_[^/]+)\.lean$",
    re.I,
)


@dataclass
class LeanRef:
    bold: str
    import_path: str
    resolved: Path


def has_lean_section(text: str) -> bool:
    return bool(LEAN_SECTION.search(text) or BULLET_LEAN.search(text))


def is_conformant(text: str) -> bool:
    return bool(ALREADY_MIGRATED.search(text))


def first_lean_bullet_pos(text: str) -> int | None:
    m = BULLET_LEAN.search(text)
    return m.start() if m else None


def split_md(text: str) -> tuple[str, str, str]:
    """Return (title_line, human_body, lean_section_tail)."""
    m = TITLE.search(text)
    if not m:
        raise ValueError("missing # title")
    title = m.group(1)
    rest = text[m.end() :]
    lm = LEAN_SECTION.search(rest)
    if lm:
        human = rest[: lm.start()].strip("\n")
        lean_tail = rest[lm.start() :]
        return title, human, lean_tail
    bullet_at = first_lean_bullet_pos(rest)
    if bullet_at is not None:
        human = rest[:bullet_at].strip("\n")
        lean_tail = rest[bullet_at:]
        return title, human, lean_tail
    raise ValueError("missing **Lean section or lean bullet list")


def default_bold(md_path: Path, rel_import: str) -> str:
    target = (md_path.parent / rel_import).resolve()
    try:
        rel = str(target.relative_to(DT)).replace("\\", "/")
    except ValueError:
        rel = rel_import
    return rel if rel.startswith("DomainTheory/") else f"DomainTheory/{rel}"


def collect_lean_refs(md_path: Path, lean_tail: str) -> list[LeanRef]:
    refs: list[LeanRef] = []
    seen: set[str] = set()

    for label, rel in BULLET_LEAN.findall(lean_tail):
        if rel in seen:
            continue
        seen.add(rel)
        resolved = (md_path.parent / rel).resolve()
        if not resolved.is_file():
            rooted = (ROOT / rel).resolve()
            if rooted.is_file():
                resolved = rooted
            else:
                raise FileNotFoundError(f"{md_path}: missing {rel}")
        bold = default_bold(md_path, rel)
        if label.strip().startswith("DomainTheory/"):
            bold = label.strip()
        refs.append(LeanRef(bold=bold, import_path=rel, resolved=resolved))

    for rel in IMPORT_LEAN.findall(lean_tail):
        if rel in seen:
            continue
        seen.add(rel)
        resolved = (md_path.parent / rel).resolve()
        if not resolved.is_file():
            rooted = (ROOT / rel).resolve()
            if rooted.is_file():
                resolved = rooted
            else:
                raise FileNotFoundError(f"{md_path}: missing {rel}")
        bold = default_bold(md_path, rel)
        refs.append(LeanRef(bold=bold, import_path=rel, resolved=resolved))

    return refs


def sidecar_stems(md_path: Path, refs: list[LeanRef]) -> tuple[str, str]:
    """Return (english_stem, concordance_stem) without extension."""
    if len(refs) == 1:
        return refs[0].resolved.stem, refs[0].resolved.stem
    return md_path.stem, md_path.stem


def rel_from_md(md_path: Path, target: Path) -> str:
    return os.path.relpath(target, md_path.parent).replace("\\", "/")


def ai_sidecar_import(md_path: Path, lean: Path) -> str | None:
    sidecar = lean.with_suffix(".ai_lean_to_english")
    if not sidecar.is_file():
        return None
    return rel_from_md(md_path, sidecar)


def build_md(
    title: str,
    english_stem: str,
    refs: list[LeanRef],
    md_path: Path,
) -> str:
    lines = [title, "", "## Human-English", "", f'@import "{english_stem}.english" {{code_block=false}}', ""]

    lines.extend(["## AI: Human-English to AI-Lean", ""])
    for ref in refs:
        lines.append(f"**{ref.bold}**")
        lines.append("")
        lines.append(f'@import "{ref.import_path}"')
        lines.append("")

    lines.extend(["## AI: AI-Lean to AI-English", ""])
    for ref in refs:
        imp = ai_sidecar_import(md_path, ref.resolved)
        if imp:
            lines.append(f'@import "{imp}" {{code_block=false}}')
            lines.append("")

    lines.extend(
        [
            "## AI: AI-English to Human-English Concordance",
            "",
            f'@import "{english_stem}.ai_english_concordance" {{code_block=false}}',
            "",
        ]
    )
    return "\n".join(lines)


def migrate_file(md_path: Path, dry_run: bool) -> str:
    if md_path.resolve() in {p.resolve() for p in SKIP_MD}:
        return "skip_model_reference"
    text = md_path.read_text(encoding="utf-8")
    if not has_lean_section(text):
        return "skip_no_lean"
    if is_conformant(text):
        return "skip_conformant"

    title, human, lean_tail = split_md(text)
    refs = collect_lean_refs(md_path, lean_tail)
    if not refs:
        raise ValueError(f"{md_path}: no lean references found")

    english_stem, _ = sidecar_stems(md_path, refs)
    english_path = md_path.with_name(f"{english_stem}.english")
    if dry_run:
        return f"would_migrate ({len(refs)} leans, stem={english_stem})"

    new_md = build_md(title, english_stem, refs, md_path)

    if human.strip():
        english_path.write_text(human.strip() + "\n", encoding="utf-8")
    elif not english_path.is_file():
        english_path.write_text("\n", encoding="utf-8")

    md_path.write_text(new_md, encoding="utf-8")
    return f"migrated ({len(refs)} leans, stem={english_stem})"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--only", type=Path, help="single .md under DomainTheory/")
    args = parser.parse_args()

    paths: list[Path]
    if args.only:
        p = args.only.resolve()
        if not p.is_file():
            print(f"not found: {p}", file=sys.stderr)
            return 1
        paths = [p]
    else:
        paths = sorted(DT.rglob("*.md"))

    counts: dict[str, int] = {}
    errors: list[str] = []

    for md_path in paths:
        try:
            status = migrate_file(md_path, args.dry_run)
            counts[status.split()[0]] = counts.get(status.split()[0], 0) + 1
        except Exception as e:
            errors.append(f"{md_path.relative_to(ROOT)}: {e}")

    print("Results:", counts)
    if errors:
        print(f"\n{len(errors)} error(s):", file=sys.stderr)
        for err in errors[:50]:
            print(err, file=sys.stderr)
        if len(errors) > 50:
            print(f"... and {len(errors) - 50} more", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
