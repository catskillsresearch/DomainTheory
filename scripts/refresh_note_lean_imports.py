#!/usr/bin/env python3
"""Retarget note ``@import`` / Lean link blocks to files that exist on disk.

Used before flattening ``arxiv.md``. When a Pref companion was folded away
(``Pref_suffix.lean`` deleted), rewrite the note to ``Pref_more.lean`` if that
exists, else ``Pref.lean``. Deduplicate repeated import blocks for the same
target. Does not invent new Lean sources — only repairs broken paths.
"""
from __future__ import annotations

import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
NOTE_ROOT = ROOT / "DomainTheory"

# Link + @import block for a Lean file (optional blank line between).
LEAN_BLOCK_RE = re.compile(
    r"\*\*\[(?P<label>[^\]]*)\]\((?P<link>[^)]+\.lean)\)\*\*\n+"
    r'@import\s+"(?P<imp>[^"]+\.lean)"\s*\n',
)

# Link without a following @import (chapter index lists).
LEAN_LINK_RE = re.compile(
    r"\*\*\[(?P<label>[^\]]*)\]\((?P<link>[^)]+\.lean)\)\*\*"
    r"(?!\n+@import)",
)


def resolve_import(note_dir: Path, rel: str) -> Path:
    return (note_dir / rel).resolve()


def retarget_missing(note_dir: Path, rel: str) -> str | None:
    """If ``rel`` is missing, return a replacement relative path, else None."""
    target = resolve_import(note_dir, rel)
    if target.is_file():
        return None
    name = Path(rel).name
    if not name.endswith(".lean"):
        return None
    stem = name[: -len(".lean")]
    parent_dir = resolve_import(note_dir, str(Path(rel).parent)) if "/" in rel or rel.startswith("../") else note_dir

    # Pref_suffix → Pref_more.lean or Pref.lean in the same directory as the missing file
    # would have lived (note-relative parent of rel).
    search_dir = (note_dir / Path(rel).parent).resolve()
    if "_" in stem:
        # longest Pref prefix that has Pref.lean or Pref_more.lean
        parts = stem.split("_")
        for i in range(len(parts) - 1, 0, -1):
            pref = "_".join(parts[:i])
            for cand in (f"{pref}_more.lean", f"{pref}.lean"):
                if (search_dir / cand).is_file():
                    # preserve relative directory of original import
                    return str(Path(rel).with_name(cand))
    # bare missing name: nothing to do
    return None


def sync_label(label: str, old_rel: str, new_rel: str) -> str:
    old_base = Path(old_rel).name
    new_base = Path(new_rel).name
    if old_base in label:
        return label.replace(old_base, new_base)
    return re.sub(r"[^/\]]+\.lean$", new_base, label)


def refresh_note(path: Path) -> bool:
    text = path.read_text(encoding="utf-8")
    note_dir = path.parent
    changed = False

    def repl_block(m: re.Match[str]) -> str:
        nonlocal changed
        imp = m.group("imp")
        link = m.group("link")
        new_imp = retarget_missing(note_dir, imp)
        new_link = retarget_missing(note_dir, link)
        # Prefer retarget of the import path; keep link in sync
        target = new_imp or (None if new_link is None and resolve_import(note_dir, imp).is_file() else new_link)
        if target is None:
            # still missing with no retarget — drop the block
            if not resolve_import(note_dir, imp).is_file():
                changed = True
                return ""
            return m.group(0)
        if target != imp or (new_link and new_link != link):
            changed = True
            link_out = new_link or target
            # label: replace basename in label if present
            label = m.group("label")
            label = sync_label(label, imp, target)
            return (
                f"**[{label}]({link_out})**\n\n"
                f'@import "{target}"\n'
            )
        return m.group(0)

    def repl_link(m: re.Match[str]) -> str:
        nonlocal changed
        link = m.group("link")
        if resolve_import(note_dir, link).is_file():
            return m.group(0)
        target = retarget_missing(note_dir, link)
        if target is None:
            changed = True
            return ""
        if target != link:
            changed = True
            label = sync_label(m.group("label"), link, target)
            return f"**[{label}]({target})**"
        return m.group(0)

    new_text = LEAN_LINK_RE.sub(repl_link, text)
    new_text = LEAN_BLOCK_RE.sub(repl_block, new_text)

    # Deduplicate identical consecutive Lean import blocks
    seen_order: list[str] = []
    blocks: dict[str, str] = {}

    def collect(m: re.Match[str]) -> str:
        key = m.group("imp")
        # normalize key to basename+dir of import
        if key not in blocks:
            seen_order.append(key)
            blocks[key] = m.group(0)
            return m.group(0)
        # duplicate — drop
        nonlocal_changed.append(True)
        return ""

    nonlocal_changed: list[bool] = []
    deduped = LEAN_BLOCK_RE.sub(collect, new_text)
    if nonlocal_changed:
        changed = True
        new_text = deduped

    # Deduplicate link-only lines pointing at the same .lean (after retarget).
    seen_links: set[str] = set()

    def dedupe_link(m: re.Match[str]) -> str:
        nonlocal changed
        link = m.group("link")
        if link in seen_links:
            changed = True
            return ""
        seen_links.add(link)
        return m.group(0)

    deduped_links = LEAN_LINK_RE.sub(dedupe_link, new_text)
    if deduped_links != new_text:
        new_text = deduped_links

    # Collapse excess blank lines
    collapsed = re.sub(r"\n{3,}", "\n\n", new_text)
    if collapsed != new_text:
        changed = True
        new_text = collapsed

    if changed and new_text != text:
        path.write_text(new_text, encoding="utf-8")
        return True
    return False


def refresh_all(note_root: Path = NOTE_ROOT) -> int:
    n = 0
    for path in sorted(note_root.rglob("*.md")):
        if refresh_note(path):
            n += 1
            print(f"  refreshed {path.relative_to(ROOT)}")
    return n


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=NOTE_ROOT,
        help="note tree root (default: DomainTheory/)",
    )
    args = parser.parse_args(argv)
    root = args.root if args.root.is_absolute() else ROOT / args.root
    print(f"==> Refreshing Lean @imports under {root.relative_to(ROOT)}")
    n = refresh_all(root)
    print(f"updated {n} notes")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
