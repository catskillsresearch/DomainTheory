#!/usr/bin/env python3
"""Rewrite markdown link targets under DomainTheory/ to paths relative to each .md file."""

from __future__ import annotations

import argparse
import os
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
NOTE_ROOT = ROOT / "DomainTheory"
LINK = re.compile(r"\[([^\]]*)\]\(([^)]+)\)")


def is_skipped_href(href: str) -> bool:
    h = href.strip()
    if not h or h.startswith("#"):
        return True
    lower = h.lower()
    return lower.startswith(("http://", "https://", "mailto:", "data:"))


def resolve_repo_target(href: str) -> Path | None:
    h = href.replace("\\", "/")
    if not h.startswith("DomainTheory/"):
        return None
    p = ROOT / h
    return p if p.is_file() else None


def relativize_href(href: str, md_dir: Path) -> str | None:
    if is_skipped_href(href):
        return None
    target = resolve_repo_target(href)
    if target is None:
        return None
    rel = Path(os.path.relpath(target, md_dir)).as_posix()
    if rel == href.replace("\\", "/"):
        return None
    return rel


def sync_label(label: str, old_href: str, new_href: str) -> str:
    old_n = old_href.replace("\\", "/")
    lab = label.strip()
    if lab == old_n or lab.startswith("DomainTheory/"):
        return new_href
    if old_n.endswith("/" + lab) or lab.endswith(Path(old_n).name):
        return new_href if lab.startswith("DomainTheory/") else label
    return label


def process_md(path: Path, dry_run: bool) -> bool:
    text = path.read_text(encoding="utf-8")
    md_dir = path.parent
    changed = False

    def repl(m: re.Match[str]) -> str:
        nonlocal changed
        label, href = m.group(1), m.group(2)
        new_href = relativize_href(href, md_dir)
        if new_href is None:
            return m.group(0)
        changed = True
        new_label = sync_label(label, href, new_href)
        return f"[{new_label}]({new_href})"

    new_text = LINK.sub(repl, text)
    if changed and not dry_run:
        path.write_text(new_text, encoding="utf-8")
    return changed


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--root", type=Path, default=NOTE_ROOT)
    args = ap.parse_args()
    root = args.root if args.root.is_absolute() else ROOT / args.root
    paths = sorted(root.rglob("*.md"))
    top = ROOT / "DomainTheory.md"
    if top.is_file():
        paths.append(top)
    n = 0
    for p in paths:
        if "vendor" in p.parts:
            continue
        if p.name == "arxiv.md" and p.parent == ROOT:
            continue
        if process_md(p, args.dry_run):
            n += 1
            print(p.relative_to(ROOT))
    print(f"{'would update' if args.dry_run else 'updated'} {n} files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
