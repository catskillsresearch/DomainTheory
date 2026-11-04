#!/usr/bin/env python3
"""Merge Functionality Pref_* companions into Retracts/*.lean owners; delete companions."""
from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RETRACTS = ROOT / "DomainTheory" / "DataTypesAsLattices" / "Retracts"
FUNC = ROOT / "DomainTheory" / "DataTypesAsLattices" / "Functionality"
DTAL = "DomainTheory.DataTypesAsLattices"
RETRACTS_P = f"{DTAL}.Retracts"
FUNC_P = f"{DTAL}.Functionality"

# owner -> extra companion stems (without .lean) beyond owner_*
EXTRA: dict[str, list[str]] = {
    "updateEnv": ["updateEnv_isScottContinuous_t", "updateEnvUnion"],
    "expR": ["expR_isRetract"],
    "expF": ["expF_isScottContinuous"],
    "lambR": ["lambR_isRetract"],
    "lambF": ["lambF_isScottContinuous"],
    "treeR": ["treeR_isRetract"],
    "treeF": ["treeF_isScottContinuous"],
}

OWNERS = [
    "plusR",
    "plus7",
    "tensorR",
    "tensor4",
    "seq4",
    "tagInj",
    "updateEnv",
    "envR",
    "expR",
    "expF",
    "lambR",
    "lambF",
    "treeR",
    "treeF",
]

# fold into Retracts/arrowR_more.lean
ARROW_MORE = ["arrowR_diag_isScottContinuous"]

IMP_RE = re.compile(r"^(?P<pub>public\s+)?import\s+(?P<mod>\S+)\s*$", re.M)

DECL_RE = re.compile(
    r"(?m)^(?P<header>(?:(?:noncomputable|protected|private|scoped|local)\s+)*"
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:noncomputable|protected|private|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev))\s+(?P<name>[A-Za-z_][\w']*)"
)


def parse_imports(text: str) -> list[str]:
    return [m.group("mod") for m in IMP_RE.finditer(text)]


def rewrite_identifiers(text: str, renames: list[tuple[str, str]]) -> str:
    for old, new in sorted(renames, key=lambda p: -len(p[0])):
        text = re.sub(rf"\b{re.escape(old)}\b", new, text)
    return text


def companion_paths(pref: str) -> list[Path]:
    paths = sorted(FUNC.glob(f"{pref}_*.lean"))
    for stem in EXTRA.get(pref, []):
        p = FUNC / f"{stem}.lean"
        if p.exists():
            paths.append(p)
    # dedupe
    seen: set[Path] = set()
    out: list[Path] = []
    for p in paths:
        if p not in seen:
            seen.add(p)
            out.append(p)
    return out


def extract_companion_body(text: str, pref: str) -> str:
    m = re.search(r"namespace DomainTheory\.DataTypesAsLattices\s*\n", text)
    if not m:
        raise SystemExit(f"no namespace in companion for {pref}")
    body = text[m.end() :]
    body = re.sub(r"\nend DomainTheory\.DataTypesAsLattices\s*$", "\n", body)

    # Flatten `namespace pref_suffix` blocks (e.g. plusR_app, seq4_app, updateEnvUnion)
    while True:
        m2 = re.search(
            rf"namespace ({re.escape(pref)}_\w+)\s*\n(.*?)end \1\s*\n",
            body,
            re.S,
        )
        if not m2:
            break
        sub = m2.group(1)
        inner = m2.group(2).strip("\n") + "\n"
        inner = re.sub(rf"\b{re.escape(sub)}\.", "", inner)
        body = body[: m2.start()] + inner + body[m2.end() :]

    # updateEnvUnion: def + nested namespace
    if pref == "updateEnv":
        body = re.sub(r"\bdef updateEnvUnion\b", "def union", body)
        body = re.sub(
            rf"\nnamespace updateEnvUnion\s*\n(.*?)\nend updateEnvUnion\s*\n",
            r"\n\1\n",
            body,
            flags=re.S,
        )
        body = re.sub(r"\bupdateEnvUnion\b", "union", body)

    # Rename Pref_foo declarations to foo
    def repl(dm: re.Match) -> str:
        name = dm.group("name")
        if name.startswith(pref + "_"):
            return f"{dm.group('header')} {name[len(pref) + 1 :]}"
        return dm.group(0)

    body = DECL_RE.sub(repl, body)

    # Internal references: pref_suffix. -> (same namespace)
    for sub in re.findall(rf"\b{re.escape(pref)}_\w+\.", body):
        body = body.replace(sub, "")

    return body.strip("\n") + "\n"


def collect_renames(pref: str, paths: list[Path]) -> list[tuple[str, str]]:
    renames: list[tuple[str, str]] = []
    for p in paths:
        text = p.read_text()
        for dm in DECL_RE.finditer(text):
            name = dm.group("name")
            if name.startswith(pref + "_"):
                renames.append((name, f"{pref}.{name[len(pref) + 1 :]}"))
        for sub in re.findall(rf"namespace ({re.escape(pref)}_\w+)", text):
            suffix = sub[len(pref) + 1 :]
            for dm in DECL_RE.finditer(text):
                n = dm.group("name")
                if text.find(f"namespace {sub}") < text.find(f"theorem {n}"):
                    renames.append((f"{sub}.{n}", f"{pref}.{n}"))
    if pref == "updateEnv":
        renames.append(("updateEnvUnion", "updateEnv.union"))
        renames.append(("updateEnv_isScottContinuous_t", "updateEnv.isScottContinuous_t"))
    for stem in EXTRA.get(pref, []):
        if stem.startswith(pref + "_"):
            renames.append((stem, f"{pref}.{stem[len(pref) + 1 :]}"))
    # dedupe
    seen: set[str] = set()
    out: list[tuple[str, str]] = []
    for a, b in renames:
        if a not in seen:
            seen.add(a)
            out.append((a, b))
    return out


def rebuild_owner(pref: str, owner_path: Path, paths: list[Path]) -> None:
    if not paths:
        return
    parent_text = owner_path.read_text()
    parent_mod = f"{RETRACTS_P}.{pref}"
    delete_mods = {f"{FUNC_P}.{p.stem}" for p in paths}

    imports = parse_imports(parent_text)
    seen = set(imports) | {parent_mod} | delete_mods
    for p in paths:
        for mod in parse_imports(p.read_text()):
            if mod in delete_mods or mod == parent_mod:
                continue
            if mod not in seen:
                seen.add(mod)
                imports.append(mod)

    chunks: list[str] = []
    for p in paths:
        chunks.append(extract_companion_body(p.read_text(), pref))

    body_match = re.search(
        r"namespace DomainTheory\.DataTypesAsLattices\s*\n", parent_text
    )
    if not body_match:
        raise SystemExit(f"no namespace in {owner_path}")

    lines = parent_text.splitlines(keepends=True)
    out: list[str] = []
    i = 0
    while i < len(lines) and not lines[i].startswith("module"):
        out.append(lines[i])
        i += 1
    out.append(lines[i])
    i += 1
    mid: list[str] = []
    while i < len(lines):
        raw = lines[i]
        if IMP_RE.match(raw.rstrip("\n")):
            i += 1
            continue
        if raw.strip() == "":
            i += 1
            continue
        break
    while i < len(lines) and not lines[i].startswith("namespace DomainTheory"):
        mid.append(lines[i])
        i += 1

    out.append("\n")
    for mod in imports:
        out.append(f"public import {mod}\n")
    out.append("\n")
    out.extend(mid)

    rest = "".join(lines[i:])
    rest = re.sub(r"\nend DomainTheory\.DataTypesAsLattices\s*$", "\n", rest)
    rest = re.sub(
        rf"\nnamespace {re.escape(pref)}\s*\n.*?\nend {re.escape(pref)}\s*\n",
        "\n",
        rest,
        flags=re.S,
    )

    ns_block = f"\nnamespace {pref}\n\n" + "\n".join(chunks) + f"\nend {pref}\n"
    new_text = (
        "".join(out) + rest.rstrip() + "\n" + ns_block + "\nend DomainTheory.DataTypesAsLattices\n"
    )
    owner_path.write_text(new_text)


def rebuild_arrow_more(paths: list[Path]) -> None:
    pref = "arrowR"
    owner_path = RETRACTS / "arrowR_more.lean"
    parent_text = owner_path.read_text()
    delete_mods = {f"{FUNC_P}.{p.stem}" for p in paths}

    imports = parse_imports(parent_text)
    seen = set(imports) | delete_mods
    for p in paths:
        for mod in parse_imports(p.read_text()):
            if mod in delete_mods:
                continue
            if mod not in seen:
                seen.add(mod)
                imports.append(mod)

    chunks = [extract_companion_body(p.read_text(), pref) for p in paths]

    lines = parent_text.splitlines(keepends=True)
    out: list[str] = []
    i = 0
    while i < len(lines) and not lines[i].startswith("module"):
        out.append(lines[i])
        i += 1
    out.append(lines[i])
    i += 1
    mid: list[str] = []
    while i < len(lines):
        raw = lines[i]
        if IMP_RE.match(raw.rstrip("\n")):
            i += 1
            continue
        if raw.strip() == "":
            i += 1
            continue
        break
    while i < len(lines) and not lines[i].startswith("namespace DomainTheory"):
        mid.append(lines[i])
        i += 1

    out.append("\n")
    for mod in imports:
        out.append(f"public import {mod}\n")
    out.append("\n")
    out.extend(mid)

    rest = "".join(lines[i:])
    rest = re.sub(r"\nend DomainTheory\.DataTypesAsLattices\s*$", "\n", rest)
    # insert before `end arrowR` inside file
    insert = "\n".join(chunks)
    if "theorem diag_isScottContinuous" not in rest and insert.strip():
        rest = rest.replace(
            "\nend arrowR\n",
            "\n" + insert + "\nend arrowR\n",
            1,
        )
    new_text = "".join(out) + rest.rstrip() + "\nend DomainTheory.DataTypesAsLattices\n"
    owner_path.write_text(new_text)


def rewrite_imports(deleted: set[str], parent_of: dict[str, str]) -> int:
    files = list((ROOT / "DomainTheory").rglob("*.lean"))
    files += list((ROOT / "DomainTheory").rglob("*.md"))
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
            text = text.replace(f"/Functionality/{old_file}", f"/Retracts/{new_file}")
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


def move_eq_files() -> list[Path]:
    moved: list[Path] = []
    for p in sorted(FUNC.glob("eq_4_*.lean")):
        dest = RETRACTS / p.name
        text = p.read_text()
        text = re.sub(
            rf"Functionality\.(plusR|tensorR|seq4|plus7|arrowR|envR|expR|lambR|treeR)_",
            r"Retracts.\1.",
            text,
        )
        # import path retargets for deleted companions happen in rename pass
        dest.write_text(text)
        p.unlink()
        moved.append(dest)
    return moved


def merge_theorem_4_5_sum() -> None:
    src = FUNC / "theorem_4_5_sum.lean"
    if not src.exists():
        return
    body = extract_companion_body(src.read_text(), "theorem_4_5")
    # theorem is named theorem_4_5_sum at top level — keep name
    dest = RETRACTS / "theorem_4_5.lean"
    text = dest.read_text()
    if "theorem_4_5_sum" in text:
        src.unlink()
        return
    imports = parse_imports(text) + parse_imports(src.read_text())
    seen: set[str] = set()
    uniq: list[str] = []
    for m in imports:
        if m.endswith(".theorem_4_5_sum") or m in seen:
            continue
        seen.add(m)
        uniq.append(m)
    # rebuild imports block
    lines = text.splitlines(keepends=True)
    out: list[str] = []
    i = 0
    while i < len(lines):
        if IMP_RE.match(lines[i].rstrip("\n")):
            i += 1
            continue
        if lines[i].startswith("module"):
            out.append(lines[i])
            i += 1
            out.append("\n")
            for mod in uniq:
                pub = "public " if not mod.startswith("DomainTheory") or "bot_isRetract" not in mod else ""
                if "bot_isRetract" in mod:
                    out.append(f"import {mod}\n")
                else:
                    out.append(f"public import {mod}\n")
            out.append("\n")
            continue
        out.append(lines[i])
        i += 1
    new_text = "".join(out)
    new_text = new_text.replace(
        "\nend DomainTheory.DataTypesAsLattices\n",
        f"\nnamespace theorem_4_5\n\n{body}\nend theorem_4_5\n\nend DomainTheory.DataTypesAsLattices\n",
    )
    dest.write_text(new_text)
    src.unlink()


def move_theorem_4_4() -> None:
    src = FUNC / "theorem_4_4.lean"
    dest = RETRACTS / "theorem_4_4.lean"
    if not src.exists():
        return
    text = src.read_text()
    text = text.replace("Functionality.tensorR_app", "Retracts.tensorR")
    text = text.replace("Functionality.", "Functionality.")  # keep other functionality imports
    dest.write_text(text)
    src.unlink()


def main() -> None:
    all_renames: list[tuple[str, str]] = []
    deleted: set[str] = set()
    parent_of: dict[str, str] = {}

    for pref in OWNERS:
        paths = companion_paths(pref)
        if not paths:
            print(f"{pref}: no companions")
            continue
        owner = RETRACTS / f"{pref}.lean"
        if not owner.exists():
            print(f"SKIP missing owner {owner}")
            continue
        renames = collect_renames(pref, paths)
        all_renames.extend(renames)
        rebuild_owner(pref, owner, paths)
        parent_mod = f"{RETRACTS_P}.{pref}"
        for p in paths:
            mod = f"{FUNC_P}.{p.stem}"
            deleted.add(mod)
            parent_of[mod] = parent_mod
            p.unlink()
        print(f"{pref}: merged {len(paths)} companions")

    arrow_paths = [FUNC / f"{s}.lean" for s in ARROW_MORE if (FUNC / f"{s}.lean").exists()]
    if arrow_paths:
        all_renames.append(
            ("arrowR_diag_isScottContinuous", "arrowR.diag_isScottContinuous")
        )
        rebuild_arrow_more(arrow_paths)
        for p in arrow_paths:
            mod = f"{FUNC_P}.{p.stem}"
            deleted.add(mod)
            parent_of[mod] = f"{RETRACTS_P}.arrowR_more"
            p.unlink()
        print(f"arrowR_more: merged {len(arrow_paths)}")

    move_eq_files()
    merge_theorem_4_5_sum()
    move_theorem_4_4()

    # Fix companion imports in moved eq files
    for p in RETRACTS.glob("eq_4_*.lean"):
        if p.name == "eq_4_11.lean":
            continue
        text = p.read_text()
        for old_mod, new_mod in parent_of.items():
            text = re.sub(
                rf"^((?:public\s+)?)import\s+{re.escape(old_mod)}\s*$",
                rf"\1import {new_mod}",
                text,
                flags=re.M,
            )
        text = text.replace(f"{FUNC_P}.", f"{RETRACTS_P}.")
        p.write_text(text)

    n = rewrite_imports(deleted, parent_of)
    print(f"rewrote imports in {n} files")

    files = list((ROOT / "DomainTheory").rglob("*.lean"))
    files += list((ROOT / "DomainTheory").rglob("*.md"))
    files.append(ROOT / "DomainTheory.lean")
    # plusR_app.app style renames
    extra: list[tuple[str, str]] = []
    for pref in OWNERS:
        extra.append((f"{pref}_app.app", f"{pref}.app"))
        extra.append((f"{pref}_app.bot", f"{pref}.bot"))
        extra.append((f"{pref}_app.top", f"{pref}.top"))
        for i in range(7):
            extra.append((f"plus7_app.tag{i}", f"plus7.tag{i}"))
        for i in range(4):
            extra.append((f"seq4_app.zero", f"seq4.zero"))
            extra.append((f"seq4_app.one", f"seq4.one"))
            extra.append((f"seq4_app.two", f"seq4.two"))
            extra.append((f"seq4_app.three", f"seq4.three"))
    all_renames.extend(extra)

    changed = 0
    for path in files:
        text = path.read_text(errors="ignore")
        new = rewrite_identifiers(text, all_renames)
        if new != text:
            path.write_text(new)
            changed += 1
    print(f"rewrote identifiers in {changed} files")

    dt = (ROOT / "DomainTheory.lean").read_text()
    for mod in sorted(deleted, key=len, reverse=True):
        dt = re.sub(rf"^import\s+{re.escape(mod)}\s*\n", "", dt, flags=re.M)
    # eq_4 imports: Functionality -> Retracts
    for p in sorted(RETRACTS.glob("eq_4_*.lean")):
        mod = f"{RETRACTS_P}.{p.stem}"
        old = f"{FUNC_P}.{p.stem}"
        dt = dt.replace(f"import {old}", f"import {mod}")
        if f"import {mod}" not in dt and f"import {old}" in dt:
            pass
    (ROOT / "DomainTheory.lean").write_text(dt)

    leftover = companion_paths("plusR")  # any owner
    for pref in OWNERS:
        for p in FUNC.glob(f"{pref}_*.lean"):
            print(f"LEFTOVER: {p}")


if __name__ == "__main__":
    main()
