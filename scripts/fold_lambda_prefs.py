#!/usr/bin/env python3
"""In-place Pref→namespace fold for Lambda (and Lambda funOf_ → Graph.funOf).

Keeps Pref_suffix.lean files, renames theorems to `suffix` under `namespace Pref`,
and rewrites callers to dotted `Pref.suffix`. Avoids import cycles from merging.
"""
from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LAMBDA = ROOT / "DomainTheory" / "DataTypesAsLattices" / "Lambda"

PARENTS = [
    "condC",
    "curry2",
    "curry3",
    "dcondSet",
    "dollarC",
    "dollarStep",
    "dollarStepBody",
    "funOf",
    "interC",
    "interp",
    "ofComb",
    "predSet",
    "primRecStep",
]

DECL_RE = re.compile(
    r"(?m)^(?P<header>(?:(?:noncomputable|protected|private|scoped|local)\s+)*"
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:noncomputable|protected|private|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev))\s+(?P<name>[A-Za-z_][\w']*)"
)


def rewrite_identifiers(text: str, renames: list[tuple[str, str]]) -> str:
    for old, new in sorted(renames, key=lambda p: -len(p[0])):
        text = re.sub(rf"\b{re.escape(old)}\b", new, text)
    return text


def convert_pref_file(path: Path, pref: str, renames: list[tuple[str, str]]) -> None:
    text = path.read_text()
    m = re.search(r"namespace DomainTheory\.DataTypesAsLattices\s*\n", text)
    if not m:
        raise SystemExit(f"no namespace: {path}")
    head = text[: m.end()]
    body = text[m.end() :]
    body = re.sub(r"\nend DomainTheory\.DataTypesAsLattices\s*$", "\n", body)

    # Rename Pref_suffix decls to suffix
    def repl(dm: re.Match) -> str:
        name = dm.group("name")
        if name.startswith(pref + "_"):
            return f"{dm.group('header')} {name[len(pref) + 1 :]}"
        return dm.group(0)

    body = DECL_RE.sub(repl, body)
    body = rewrite_identifiers(body, renames)

    # Qualify Graph.beta when a theorem named beta is in this namespace
    if pref == "condC":
        # After rename, theorem beta's proof may call Graph.beta
        body = re.sub(
            r"(theorem beta\b[\s\S]*?:=\s*\n\s*)beta\b",
            r"\1_root_.DomainTheory.DataTypesAsLattices.beta",
            body,
            count=1,
        )
        body = re.sub(
            r"(exact )beta\b",
            r"\1_root_.DomainTheory.DataTypesAsLattices.beta",
            body,
        )

    new_text = (
        head
        + f"\nnamespace {pref}\n\n"
        + body.rstrip()
        + f"\n\nend {pref}\n\n"
        + "end DomainTheory.DataTypesAsLattices\n"
    )
    path.write_text(new_text)


def main() -> None:
    renames: list[tuple[str, str]] = []
    pref_paths: list[tuple[str, Path]] = []
    for pref in PARENTS:
        for path in sorted(LAMBDA.glob(f"{pref}_*.lean")):
            pref_paths.append((pref, path))
            # discover decl names
            for dm in DECL_RE.finditer(path.read_text()):
                name = dm.group("name")
                if name.startswith(pref + "_"):
                    renames.append((name, f"{pref}.{name[len(pref) + 1 :]}"))

    print(f"Pref files: {len(pref_paths)}; renames: {len(renames)}")
    for old, new in renames:
        print(f"  {old} → {new}")

    for pref, path in pref_paths:
        convert_pref_file(path, pref, renames)
        print(f"converted {path.relative_to(ROOT)}")

    # Rewrite callers (not the Pref files again — already done; rewriting again is idempotent for dotted)
    files = list((ROOT / "DomainTheory").rglob("*.lean"))
    files += list((ROOT / "DomainTheory").rglob("*.md"))
    files += list((ROOT / "DomainTheory").rglob("*.mermaid"))
    files.append(ROOT / "DomainTheory.lean")

    pref_set = {p for _, p in pref_paths}
    changed = 0
    for path in files:
        if path in pref_set:
            continue
        text = path.read_text(errors="ignore")
        new = rewrite_identifiers(text, renames)
        if new != text:
            path.write_text(new)
            changed += 1
    print(f"rewrote {changed} caller files")

    # leftover?
    leftover = []
    for old, _ in renames:
        for path in (ROOT / "DomainTheory").rglob("*.lean"):
            if re.search(rf"\b{re.escape(old)}\b", path.read_text(errors="ignore")):
                leftover.append((old, path))
                break
    if leftover:
        print(f"WARNING leftover ({len(leftover)}):")
        for old, path in leftover[:30]:
            print(f"  {old} in {path}")
    else:
        print("no leftover Pref theorem names")


if __name__ == "__main__":
    main()
