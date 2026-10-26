#!/usr/bin/env python3
"""In-place Pref→namespace fold for DataTypesAsLattices/Computability.

Keeps Pref_suffix.lean files; puts decls under `namespace Pref` as `suffix`;
rewrites callers to Pref.suffix without mangling import module paths.
"""
from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
COMP = ROOT / "DomainTheory" / "DataTypesAsLattices" / "Computability"

PARENTS = [
    "pack4",
    "pairComb",
    "precC",
    "precEnv",
    "primRecComb",
    "primRecOpC",
    "theorem_2_6",
    "unpairSndC",
    "unpairFstC",
]

DECL_RE = re.compile(
    r"(?m)^(?P<header>(?:(?:noncomputable|protected|private|scoped|local)\s+)*"
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:noncomputable|protected|private|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev))\s+(?P<name>[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)"
)
IMP_LINE_RE = re.compile(r"^(?:public\s+)?import\s+\S+\s*$")


def rewrite_identifiers_safe(text: str, renames: list[tuple[str, str]]) -> str:
    """Rewrite Pref_suffix → Pref.suffix, but never touch import lines."""
    lines = text.splitlines(keepends=True)
    out: list[str] = []
    for line in lines:
        if IMP_LINE_RE.match(line.rstrip("\n")):
            out.append(line)
            continue
        for old, new in sorted(renames, key=lambda p: -len(p[0])):
            line = re.sub(rf"\b{re.escape(old)}\b", new, line)
        out.append(line)
    return "".join(out)


def discover_renames() -> tuple[list[tuple[str, Path]], list[tuple[str, str]]]:
    """Return (pref, path) list and (old_name, Pref.suffix) renames."""
    pref_paths: list[tuple[str, Path]] = []
    renames: list[tuple[str, str]] = []
    seen: set[str] = set()
    for pref in PARENTS:
        for path in sorted(COMP.glob(f"{pref}_*.lean")):
            pref_paths.append((pref, path))
            text = path.read_text()
            for dm in DECL_RE.finditer(text):
                name = dm.group("name")
                # Already dotted: theorem_2_6.fin
                if name.startswith(pref + "."):
                    suf = name[len(pref) + 1 :]
                    old = name  # already dotted; no rename of identifier needed
                    new = f"{pref}.{suf}"
                    if old not in seen:
                        # still record so we know the short name for the file convert
                        seen.add(old)
                    continue
                if name.startswith(pref + "_"):
                    suf = name[len(pref) + 1 :]
                    old, new = name, f"{pref}.{suf}"
                    if old not in seen:
                        renames.append((old, new))
                        seen.add(old)
    return pref_paths, renames


def short_name(pref: str, name: str) -> str | None:
    if name.startswith(pref + "_"):
        return name[len(pref) + 1 :]
    if name.startswith(pref + "."):
        return name[len(pref) + 1 :]
    return None


def convert_pref_file(path: Path, pref: str, renames: list[tuple[str, str]]) -> None:
    text = path.read_text()
    m = re.search(r"namespace DomainTheory\.DataTypesAsLattices\s*\n", text)
    if not m:
        raise SystemExit(f"no namespace: {path}")
    head = text[: m.end()]
    body = text[m.end() :]
    body = re.sub(r"\nend DomainTheory\.DataTypesAsLattices\s*$", "\n", body)

    # If already wrapped in namespace pref, unwrap first
    body = re.sub(rf"\nnamespace {re.escape(pref)}\s*\n", "\n", body)
    body = re.sub(rf"\nend {re.escape(pref)}\s*\n", "\n", body)

    def repl(dm: re.Match) -> str:
        name = dm.group("name")
        suf = short_name(pref, name)
        if suf is None:
            return dm.group(0)
        return f"{dm.group('header')} {suf}"

    body = DECL_RE.sub(repl, body)
    body = rewrite_identifiers_safe(body, renames)

    new_text = (
        head
        + f"\nnamespace {pref}\n\n"
        + body.rstrip()
        + f"\n\nend {pref}\n\n"
        + "end DomainTheory.DataTypesAsLattices\n"
    )
    path.write_text(new_text)


def fix_md_imports(renames: list[tuple[str, str]]) -> int:
    """If any md got Pref.suffix.lean paths, restore Pref_suffix.lean."""
    mapping = {}
    for old, new in renames:
        # new is Pref.suffix → file is Pref_suffix.lean
        pref, _, suf = new.partition(".")
        mapping[f"{pref}.{suf}.lean"] = f"{old}.lean"
    # also theorem_2_6 already-dotted files
    for path in COMP.glob("theorem_2_6_*.lean"):
        stem = path.stem  # theorem_2_6_fin
        suf = stem[len("theorem_2_6_") :]
        mapping[f"theorem_2_6.{suf}.lean"] = f"{stem}.lean"

    changed = 0
    for path in (ROOT / "DomainTheory").rglob("*"):
        if path.suffix not in {".md", ".mermaid"}:
            continue
        text = path.read_text(errors="ignore")
        orig = text
        for dotted, unders in sorted(mapping.items(), key=lambda x: -len(x[0])):
            text = text.replace(dotted, unders)
        if text != orig:
            path.write_text(text)
            changed += 1
    return changed


def main() -> None:
    pref_paths, renames = discover_renames()
    print(f"Pref files: {len(pref_paths)}; identifier renames: {len(renames)}")
    for old, new in renames:
        print(f"  {old} → {new}")

    for pref, path in pref_paths:
        convert_pref_file(path, pref, renames)
        print(f"converted {path.relative_to(ROOT)}")

    # Also wrap theorem_2_6 already-dotted files (renames may be empty for them)
    # convert_pref_file already handles theorem_2_6.* names via short_name

    pref_set = {p for _, p in pref_paths}
    files = list((ROOT / "DomainTheory").rglob("*.lean"))
    files += list((ROOT / "DomainTheory").rglob("*.md"))
    files += list((ROOT / "DomainTheory").rglob("*.mermaid"))
    files.append(ROOT / "DomainTheory.lean")

    changed = 0
    for path in files:
        if path in pref_set:
            continue
        text = path.read_text(errors="ignore")
        new = rewrite_identifiers_safe(text, renames)
        if new != text:
            path.write_text(new)
            changed += 1
    print(f"rewrote {changed} caller files")

    md_n = fix_md_imports(renames)
    print(f"fixed {md_n} md/mermaid path refs")

    # leftover Pref_ names outside import lines?
    leftover = []
    for old, _ in renames:
        for path in (ROOT / "DomainTheory").rglob("*.lean"):
            for line in path.read_text(errors="ignore").splitlines():
                if IMP_LINE_RE.match(line):
                    continue
                if re.search(rf"\b{re.escape(old)}\b", line):
                    leftover.append((old, path))
                    break
            else:
                continue
            break
    if leftover:
        print(f"WARNING leftover ({len(leftover)}):")
        for old, path in leftover[:30]:
            print(f"  {old} in {path}")
    else:
        print("no leftover Pref theorem/def names (outside imports)")


if __name__ == "__main__":
    main()
