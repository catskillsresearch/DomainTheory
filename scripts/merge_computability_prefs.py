#!/usr/bin/env python3
"""Merge Computability Pref_*.lean bodies into parent files (single namespace block), delete Prefs."""
from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
COMP = ROOT / "DomainTheory" / "DataTypesAsLattices" / "Computability"
DTAL_PREFIX = "DomainTheory.DataTypesAsLattices.Computability"

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

IMP_RE = re.compile(r"^(?P<pub>public\s+)?import\s+(?P<mod>\S+)\s*$", re.M)


def parse_imports(text: str) -> list[str]:
    return [m.group("mod") for m in IMP_RE.finditer(text)]


def extract_pref_inner(text: str, pref: str) -> str:
    """Content inside `namespace Pref` ... `end Pref`, stripped."""
    m = re.search(
        rf"namespace {re.escape(pref)}\s*\n(.*)\nend {re.escape(pref)}\s*\n",
        text,
        re.S,
    )
    if not m:
        raise SystemExit(f"missing namespace {pref}")
    body = m.group(1).strip("\n")
    # Drop repeated open / attribute lines we'll hoist once — keep them in first chunk only later
    return body


def split_opens_and_rest(body: str) -> tuple[list[str], str]:
    """Pull leading open/attribute lines out of a Pref body."""
    lines = body.splitlines()
    opens: list[str] = []
    i = 0
    while i < len(lines):
        s = lines[i].strip()
        if s == "" and not opens:
            i += 1
            continue
        if s.startswith("open ") or s.startswith("attribute "):
            opens.append(lines[i])
            i += 1
            continue
        break
    rest = "\n".join(lines[i:]).strip("\n")
    return opens, rest


def rebuild_parent(pref: str) -> list[Path]:
    parent_path = COMP / f"{pref}.lean"
    pref_paths = sorted(COMP.glob(f"{pref}_*.lean"))
    parent_text = parent_path.read_text()
    parent_mod = f"{DTAL_PREFIX}.{pref}"
    delete_mods = {f"{DTAL_PREFIX}.{p.stem}" for p in pref_paths}

    # Collect imports
    imports = parse_imports(parent_text)
    seen = set(imports) | {parent_mod} | delete_mods
    for p in pref_paths:
        for mod in parse_imports(p.read_text()):
            if mod not in seen:
                seen.add(mod)
                imports.append(mod)

    # Collect bodies
    all_opens: list[str] = []
    open_seen: set[str] = set()
    chunks: list[str] = []
    for p in pref_paths:
        inner = extract_pref_inner(p.read_text(), pref)
        opens, rest = split_opens_and_rest(inner)
        for o in opens:
            key = o.strip()
            if key not in open_seen:
                open_seen.add(key)
                all_opens.append(o)
        if rest.strip():
            chunks.append(rest.strip() + "\n")

    # Rebuild parent: keep header through def (everything before final end DomainTheory...)
    # Strip trailing end
    body_match = re.search(
        r"namespace DomainTheory\.DataTypesAsLattices\s*\n", parent_text
    )
    if not body_match:
        raise SystemExit(f"no namespace in {parent_path}")

    # Reconstruct from scratch for clarity
    # Preserve set_option / docs from parent after imports
    pre = parent_text[: body_match.end()]
    # Replace import block in pre
    lines = parent_text.splitlines(keepends=True)
    out: list[str] = []
    i = 0
    while i < len(lines) and not lines[i].startswith("module"):
        out.append(lines[i])
        i += 1
    out.append(lines[i])  # module
    i += 1
    # skip old imports and blanks until @[expose] or set_option or namespace
    mid: list[str] = []
    while i < len(lines):
        raw = lines[i]
        if IMP_RE.match(raw.rstrip("\n")):
            i += 1
            continue
        if raw.strip() == "":
            # keep single blanks in mid later
            i += 1
            continue
        break
    while i < len(lines) and not lines[i].startswith("namespace DomainTheory"):
        mid.append(lines[i])
        i += 1
    # emit imports
    out.append("\n")
    for mod in imports:
        out.append(f"public import {mod}\n")
    out.append("\n")
    out.extend(mid)
    if not mid or not mid[-1].endswith("\n"):
        pass
    # namespace line
    out.append("namespace DomainTheory.DataTypesAsLattices\n")
    i += 1  # skip original namespace

    # rest of parent until end
    rest = "".join(lines[i:])
    rest = re.sub(r"\nend DomainTheory\.DataTypesAsLattices\s*$", "\n", rest)
    # If parent already has namespace pref, strip it so we rewrite once
    rest = re.sub(
        rf"\nnamespace {re.escape(pref)}\s*\n.*?\nend {re.escape(pref)}\s*\n",
        "\n",
        rest,
        flags=re.S,
    )

    ns_block = f"\nnamespace {pref}\n\n"
    if all_opens:
        ns_block += "\n".join(all_opens) + "\n\n"
    ns_block += "\n".join(chunks)
    if not ns_block.endswith("\n"):
        ns_block += "\n"
    ns_block += f"\nend {pref}\n"

    new_text = "".join(out) + rest.rstrip() + "\n" + ns_block + "\nend DomainTheory.DataTypesAsLattices\n"
    # Fix primRecComb.ofNat shadowing if present
    if pref == "primRecComb":
        new_text = new_text.replace(
            "funOf (primRecComb a f) (ofNat n) = primRecVal a f n",
            "funOf (primRecComb a f) (_root_.DomainTheory.DataTypesAsLattices.ofNat n) =\n"
            "      primRecVal a f n",
        )
        new_text = new_text.replace(
            "rw [← hgraph, hfix, ← eq_2_27, primRecHat_ofNat]",
            "rw [← hgraph, hfix, ← _root_.DomainTheory.DataTypesAsLattices.eq_2_27,\n"
            "    primRecHat_ofNat]",
        )
        # already-qualified variant from prior fix
        new_text = new_text.replace(
            "funOf (primRecComb a f) (_root_.DomainTheory.DataTypesAsLattices.ofNat n) =\n"
            "      primRecVal a f n := by\n"
            "  have hgraph := primRecStep.graph_of a f\n"
            "  have hfix := theorem_2_5 (primRecStep.isScottContinuous a f)\n"
            "  simp only [primRecComb]\n"
            "  rw [← hgraph, hfix, ← eq_2_27, primRecHat_ofNat]",
            "funOf (primRecComb a f) (_root_.DomainTheory.DataTypesAsLattices.ofNat n) =\n"
            "      primRecVal a f n := by\n"
            "  have hgraph := primRecStep.graph_of a f\n"
            "  have hfix := theorem_2_5 (primRecStep.isScottContinuous a f)\n"
            "  simp only [primRecComb]\n"
            "  rw [← hgraph, hfix, ← _root_.DomainTheory.DataTypesAsLattices.eq_2_27,\n"
            "    primRecHat_ofNat]",
        )

    parent_path.write_text(new_text)
    for p in pref_paths:
        p.unlink()
    return pref_paths


def rewrite_imports(deleted: set[str], parent_of: dict[str, str]) -> int:
    """Replace import Pref_suffix with import Parent; fix md @imports."""
    files = list((ROOT / "DomainTheory").rglob("*.lean"))
    files += list((ROOT / "DomainTheory").rglob("*.md"))
    files += list((ROOT / "DomainTheory").rglob("*.mermaid"))
    files.append(ROOT / "DomainTheory.lean")
    changed = 0
    for path in files:
        text = path.read_text(errors="ignore")
        orig = text
        for old_mod in deleted:
            new_mod = parent_of[old_mod]
            text = re.sub(
                rf"^((?:public\s+)?)import\s+{re.escape(old_mod)}\s*$",
                rf"\1import {new_mod}",
                text,
                flags=re.M,
            )
            old_file = old_mod.rsplit(".", 1)[-1] + ".lean"
            new_file = new_mod.rsplit(".", 1)[-1] + ".lean"
            text = text.replace(f'@import "{old_file}"', f'@import "{new_file}"')
            text = text.replace(f"]({old_file})", f"]({new_file})")
            text = text.replace(f"/{old_file})", f"/{new_file})")
            text = text.replace(f"/{old_file}]", f"/{new_file}]")
            text = text.replace(f"/{old_file}`", f"/{new_file}`")
            text = text.replace(f"/{old_file}", f"/{new_file}")
        # Deduplicate import lines
        lines = text.splitlines(keepends=True)
        out: list[str] = []
        seen: set[str] = set()
        for line in lines:
            m = IMP_RE.match(line.rstrip("\n"))
            if m:
                key = m.group("mod")
                if key in seen:
                    continue
                seen.add(key)
            out.append(line)
        text = "".join(out)
        if text != orig:
            path.write_text(text)
            changed += 1
    return changed


def main() -> None:
    deleted: set[str] = set()
    parent_of: dict[str, str] = {}
    all_deleted_paths: list[Path] = []
    for pref in PARENTS:
        paths = rebuild_parent(pref)
        parent_mod = f"{DTAL_PREFIX}.{pref}"
        for p in paths:
            mod = f"{DTAL_PREFIX}.{p.stem}"
            deleted.add(mod)
            parent_of[mod] = parent_mod
            all_deleted_paths.append(p)
        print(f"{pref}: merged {len(paths)} files → {pref}.lean; deleted {[p.name for p in paths]}")

    n = rewrite_imports(deleted, parent_of)
    print(f"rewrote imports in {n} files")

    # DomainTheory.lean: drop deleted modules
    dt = (ROOT / "DomainTheory.lean").read_text()
    for mod in sorted(deleted, key=len, reverse=True):
        dt = re.sub(rf"^import\s+{re.escape(mod)}\s*\n", "", dt, flags=re.M)
    (ROOT / "DomainTheory.lean").write_text(dt)

    leftover = list(COMP.glob("*_*"))
    leftover = [p for p in COMP.iterdir() if p.is_file() and any(p.name.startswith(f"{pref}_") for pref in PARENTS)]
    print("leftover Pref files:", [p.name for p in leftover] or "none")


if __name__ == "__main__":
    main()
