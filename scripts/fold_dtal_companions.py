#!/usr/bin/env python3
"""Merge parent_suffix.lean companions into parent.lean as parent.suffix.

Pref-fold rules (revision.mdc):
- Merge every companion into the parent; delete companion files.
- One `namespace Parent` block with short names.
- Callers use dotted Parent.suffix.
- Leave leftovers in Parent_more.lean only when merging would create an import cycle.
"""
from __future__ import annotations

import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DTAL = ROOT / "DomainTheory" / "DataTypesAsLattices"

DIRS = [
    "Lambda",
    "Retracts",
    "Closures",
    "Computability",
    "Continuous",
    "Enumeration",
    "Graph",
]

IMP_RE = re.compile(r"^(?P<pub>public\s+)?import\s+(?P<mod>\S+)\s*$", re.M)
DECL_RE = re.compile(
    r"(?m)^(?P<header>(?:(?:noncomputable|protected|private|scoped|local)\s+)*"
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:noncomputable|protected|private|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev))\s+(?P<name>[A-Za-z_][\w'.]*)"
)
NS_DTAL = "namespace DomainTheory.DataTypesAsLattices"


def parse_imports(text: str) -> list[str]:
    return [m.group("mod") for m in IMP_RE.finditer(text)]


def companion_pairs(dirpath: Path) -> list[tuple[str, str, str]]:
    """Return (companion_stem, parent_stem, suffix) using longest existing parent prefix."""
    files = {p.stem for p in dirpath.glob("*.lean")}
    out: list[tuple[str, str, str]] = []
    for stem in sorted(files):
        if "_" not in stem:
            continue
        # Never re-fold cycle leftovers as Parent_more → Parent.more
        if stem.endswith("_more"):
            continue
        parts = stem.split("_")
        for i in range(len(parts) - 1, 0, -1):
            parent = "_".join(parts[:i])
            if parent in files:
                out.append((stem, parent, "_".join(parts[i:])))
                break
    return out


def extract_dtal_body(text: str) -> str:
    m = re.search(rf"{re.escape(NS_DTAL)}\s*\n", text)
    if not m:
        # some files omit module header / start mid-import; try anyway
        raise ValueError("missing DomainTheory.DataTypesAsLattices namespace")
    body = text[m.end() :]
    body = re.sub(r"\nend DomainTheory\.DataTypesAsLattices\s*$", "\n", body)
    return body.strip("\n") + "\n"


def flatten_namespace(body: str, pref: str) -> str:
    """Unwrap `namespace pref` … `end pref`, keeping any surrounding decls."""
    # Whole body is the namespace
    m = re.search(
        rf"(?s)^\s*namespace {re.escape(pref)}\s*\n(.*)\nend {re.escape(pref)}\s*$",
        body.strip("\n"),
    )
    if m:
        return m.group(1).strip("\n") + "\n"

    def repl(mm: re.Match) -> str:
        return "\n" + mm.group(1).strip("\n") + "\n"

    return re.sub(
        rf"(?s)\nnamespace {re.escape(pref)}\s*\n(.*?)\nend {re.escape(pref)}\s*\n",
        repl,
        "\n" + body if not body.startswith("\n") else body,
    ).lstrip("\n")


def rename_long_decls(body: str, pref: str, suffix: str) -> tuple[str, list[tuple[str, str]]]:
    """Rename Pref_suffix / Pref.suffix decls to short suffix; return body + renames."""
    renames: list[tuple[str, str]] = []
    long = f"{pref}_{suffix}"
    dotted = f"{pref}.{suffix}"
    prefix_us = pref + "_"
    prefix_dot = pref + "."

    def short_of(name: str) -> str | None:
        if name == long or name.startswith(prefix_us):
            return name[len(pref) + 1 :]
        if name.startswith(prefix_dot):
            return name[len(pref) + 1 :]
        if name == suffix or name.startswith(suffix + "_") or name.startswith(suffix + "."):
            return name
        return None


    def repl(dm: re.Match) -> str:
        name = dm.group("name")
        short = short_of(name)
        if short is None:
            return dm.group(0)
        # Prefer underscore long → dotted for callers
        if "_" in name and not name.startswith(prefix_dot):
            renames.append((name, f"{pref}.{short}"))
        elif name.startswith(prefix_dot):
            # theorem_2_4.complete stays callable as theorem_2_4.complete after fold
            renames.append((name, f"{pref}.{short}"))
        else:
            renames.append((long, dotted))
        return f"{dm.group('header')} {short}"

    body2 = DECL_RE.sub(repl, body)
    # Rename long Pref_suffix refs inside this body to short (same namespace soon)
    # Longest-first among known longs for this companion file
    body2 = re.sub(rf"\b{re.escape(long)}\b", suffix, body2)
    # Pref.suffix → suffix inside the namespace body (self-refs)
    body2 = re.sub(rf"\b{re.escape(dotted)}\b", suffix, body2)
    if (long, dotted) not in renames:
        renames.append((long, dotted))
    return body2, renames


def split_opens_and_rest(body: str) -> tuple[list[str], str]:
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


def rebuild_parent(
    dirpath: Path,
    pref: str,
    companions: list[tuple[str, str]],
    *,
    as_more: bool = False,
) -> tuple[list[Path], list[tuple[str, str]]]:
    """Merge companions into parent (or parent_more). companions: (stem, suffix)."""
    parent_path = dirpath / (f"{pref}_more.lean" if as_more else f"{pref}.lean")
    if as_more and not parent_path.exists():
        # seed from thin wrapper importing parent
        mod_prefix = f"DomainTheory.DataTypesAsLattices.{dirpath.name}"
        parent_path.write_text(
            "module\n\n"
            f"public import {mod_prefix}.{pref}\n"
            "@[expose] public section\n\n"
            f"{NS_DTAL}\n\n"
            f"namespace {pref}\n\nend {pref}\n\n"
            "end DomainTheory.DataTypesAsLattices\n"
        )

    parent_text = parent_path.read_text()
    mod_prefix = f"DomainTheory.DataTypesAsLattices.{dirpath.name}"
    parent_mod = f"{mod_prefix}.{pref}_more" if as_more else f"{mod_prefix}.{pref}"
    delete_stems = {stem for stem, _ in companions}
    delete_mods = {f"{mod_prefix}.{s}" for s in delete_stems}

    imports = parse_imports(parent_text)
    seen = set(imports) | {parent_mod} | delete_mods
    if as_more:
        seen.add(f"{mod_prefix}.{pref}")
    all_renames: list[tuple[str, str]] = []
    all_opens: list[str] = []
    open_seen: set[str] = set()
    chunks: list[str] = []

    # Preserve existing `namespace pref` content (not root defs)
    for mm in re.finditer(
        rf"(?s)\nnamespace {re.escape(pref)}\s*\n(.*?)\nend {re.escape(pref)}\s*\n",
        "\n" + parent_text if not parent_text.startswith("\n") else parent_text,
    ):
        o, r = split_opens_and_rest(mm.group(1).strip("\n") + "\n")
        for line in o:
            if line.strip() not in open_seen:
                open_seen.add(line.strip())
                all_opens.append(line)
        if r.strip():
            chunks.append(r.strip() + "\n")

    for stem, suffix in sorted(companions, key=lambda x: x[0]):
        path = dirpath / f"{stem}.lean"
        text = path.read_text()
        # Skip empty Pref stubs (body already folded elsewhere)
        if "namespace DomainTheory.DataTypesAsLattices" not in text:
            path.unlink()
            all_renames.append((f"{pref}_{suffix}", f"{pref}.{suffix}"))
            continue
        # Only absorb companion imports into *_more (avoids Pref-bloat cycles).
        # Parent keeps its own imports; lemmas that need more go to _more via
        # companion_needs_more / post-build fixes.
        if as_more:
            for mod in parse_imports(text):
                if mod not in seen:
                    seen.add(mod)
                    imports.append(mod)
        try:
            body = extract_dtal_body(text)
        except ValueError as e:
            raise SystemExit(f"{path}: {e}") from e
        # Flatten namespaces for this parent and for the companion stem
        # (after a prior bottom-up fold of stem_*.lean into stem).
        body = flatten_namespace(body, pref)
        body = flatten_namespace(body, stem)
        body, renames = rename_long_decls(body, pref, suffix)
        if stem != pref:
            for dm in DECL_RE.finditer(body):
                short = dm.group("name")
                if "." in short:
                    continue
                renames.append((f"{stem}.{short}", f"{pref}.{short}"))
        all_renames.extend(renames)
        opens, rest = split_opens_and_rest(body)
        for o in opens:
            if o.strip() not in open_seen:
                open_seen.add(o.strip())
                all_opens.append(o)
        if rest.strip():
            chunks.append(rest.strip() + "\n")

    # Rebuild file
    lines = parent_text.splitlines(keepends=True)
    out: list[str] = []
    i = 0
    # keep anything before module
    while i < len(lines) and not lines[i].startswith("module"):
        out.append(lines[i])
        i += 1
    if i < len(lines) and lines[i].startswith("module"):
        out.append(lines[i])
        i += 1
    else:
        out = ["module\n", "\n"] + out
        i = 0
        lines = parent_text.splitlines(keepends=True)

    # skip old imports / blanks
    while i < len(lines):
        raw = lines[i]
        if IMP_RE.match(raw.rstrip("\n")) or raw.strip() == "":
            i += 1
            continue
        break
    mid: list[str] = []
    while i < len(lines) and not lines[i].startswith(NS_DTAL):
        mid.append(lines[i])
        i += 1

    out.append("\n")
    for mod in imports:
        out.append(f"public import {mod}\n")
    out.append("\n")
    if mid:
        # drop leading blanks in mid
        while mid and mid[0].strip() == "":
            mid.pop(0)
        out.extend(mid)
        if not mid[-1].endswith("\n"):
            out.append("\n")
    out.append(f"{NS_DTAL}\n")

    # Parent core: defs that lived outside namespace
    # Re-extract from original parent before namespace
    if i < len(lines):
        i += 1  # skip namespace line
    rest_orig = "".join(lines[i:])
    rest_orig = re.sub(r"\nend DomainTheory\.DataTypesAsLattices\s*$", "\n", rest_orig)
    rest_orig = re.sub(
        rf"(?s)\nnamespace {re.escape(pref)}\s*\n.*?\nend {re.escape(pref)}\s*\n",
        "\n",
        rest_orig,
    )
    # If as_more, don't keep unrelated core from stub
    if as_more:
        rest_orig = "\n"

    ns_block = f"\nnamespace {pref}\n\n"
    if all_opens:
        ns_block += "\n".join(all_opens) + "\n\n"
    ns_block += "\n".join(chunks)
    if not ns_block.endswith("\n"):
        ns_block += "\n"
    ns_block += f"\nend {pref}\n"

    new_text = (
        "".join(out)
        + rest_orig.rstrip()
        + "\n"
        + ns_block
        + "\nend DomainTheory.DataTypesAsLattices\n"
    )
    # Collapse excessive blank lines
    new_text = re.sub(r"\n{3,}", "\n\n", new_text)
    parent_path.write_text(new_text)

    deleted_paths = [dirpath / f"{stem}.lean" for stem, _ in companions]
    for p in deleted_paths:
        p.unlink()
    return deleted_paths, all_renames


def rewrite_identifiers(text: str, renames: list[tuple[str, str]]) -> str:
    # Only rewrite long Pref_suffix (or already-dotted) names — never bare short
    # names, which would mangle decls inside `namespace Pref`.
    safe: list[tuple[str, str]] = []
    for old, new in renames:
        if old == new:
            continue
        if "_" not in old and "." not in old:
            continue
        safe.append((old, new))
    safe.sort(key=lambda p: -len(p[0]))
    lines = text.splitlines(keepends=True)
    out: list[str] = []
    for line in lines:
        if IMP_RE.match(line.rstrip("\n")):
            out.append(line)
            continue
        new = line
        for old, new_name in safe:
            new = re.sub(rf"\b{re.escape(old)}\b", new_name, new)
        out.append(new)
    return "".join(out)


def rewrite_imports_and_refs(
    deleted: dict[str, str],
    renames: list[tuple[str, str]],
) -> int:
    """deleted: old_mod -> new_mod"""
    files = list((ROOT / "DomainTheory").rglob("*.lean"))
    files += list((ROOT / "DomainTheory").rglob("*.md"))
    files += list((ROOT / "DomainTheory").rglob("*.mermaid"))
    files.append(ROOT / "DomainTheory.lean")
    rename_map: dict[str, str] = {}
    for old, new in renames:
        if old == new:
            continue
        if "_" not in old and "." not in old:
            continue
        rename_map[old] = new
    # Longest match via alternation
    id_pat = None
    if rename_map:
        alts = sorted(rename_map.keys(), key=len, reverse=True)
        id_pat = re.compile(r"\b(" + "|".join(re.escape(a) for a in alts) + r")\b")

    del_sorted = sorted(deleted.items(), key=lambda p: -len(p[0]))
    # Precompute file-name replacements
    file_repls: list[tuple[str, str]] = []
    for old_mod, new_mod in del_sorted:
        old_file = old_mod.rsplit(".", 1)[-1] + ".lean"
        new_file = new_mod.rsplit(".", 1)[-1] + ".lean"
        if old_file != new_file:
            file_repls.append((old_file, new_file))

    changed = 0
    for path in files:
        text = path.read_text(errors="ignore")
        orig = text
        # Fast path: skip files with no deleted-mod / rename tokens
        maybe = False
        for old_mod, _ in del_sorted:
            if old_mod in text or old_mod.rsplit(".", 1)[-1] + ".lean" in text:
                maybe = True
                break
        if not maybe and id_pat is not None and id_pat.search(text):
            maybe = True
        if not maybe:
            continue

        for old_mod, new_mod in del_sorted:
            text = re.sub(
                rf"^((?:public\s+)?)import\s+{re.escape(old_mod)}\s*$",
                rf"\1import {new_mod}",
                text,
                flags=re.M,
            )
        for old_file, new_file in file_repls:
            text = text.replace(f'@import "{old_file}"', f'@import "{new_file}"')
            text = text.replace(f"]({old_file})", f"]({new_file})")
            text = text.replace(f"/{old_file})", f"/{new_file})")
            text = text.replace(f"/{old_file}]", f"/{new_file}]")
            text = text.replace(f"/{old_file}`", f"/{new_file}`")
            text = text.replace(f"/{old_file}", f"/{new_file}")

        if id_pat is not None:
            lines = text.splitlines(keepends=True)
            out_lines: list[str] = []
            for line in lines:
                if IMP_RE.match(line.rstrip("\n")):
                    out_lines.append(line)
                else:
                    out_lines.append(id_pat.sub(lambda m: rename_map[m.group(1)], line))
            text = "".join(out_lines)

        # dedupe imports
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


def fold_lambda_funof_into_graph() -> tuple[dict[str, str], list[tuple[str, str]]]:
    """Fold Graph/funOf_* into funOf; Lambda/funOf_* into Graph/funOf_more."""
    lam = DTAL / "Lambda"
    graph = DTAL / "Graph"
    mod_g = "DomainTheory.DataTypesAsLattices.Graph"
    mod_l = "DomainTheory.DataTypesAsLattices.Lambda"
    deleted: dict[str, str] = {}
    renames: list[tuple[str, str]] = []

    graph_kids = [
        (p.stem, p.stem[len("funOf_") :])
        for p in sorted(graph.glob("funOf_*.lean"))
        if not p.stem.endswith("_more")
    ]
    safe = [(s, suf) for s, suf in graph_kids if suf != "isScottContinuous"]
    more = [(s, suf) for s, suf in graph_kids if suf == "isScottContinuous"]

    for p in sorted(lam.glob("funOf_*.lean")):
        suf = p.stem[len("funOf_") :]
        dest = graph / p.name
        if dest.exists():
            raise SystemExit(f"name clash moving {p} → {dest}")
        dest.write_text(p.read_text())
        p.unlink()
        more.append((dest.stem, suf))
        deleted[f"{mod_l}.{p.stem}"] = f"{mod_g}.funOf_more"

    if safe:
        paths, rns = rebuild_parent(graph, "funOf", safe, as_more=False)
        for p in paths:
            deleted[f"{mod_g}.{p.stem}"] = f"{mod_g}.funOf"
        renames.extend(rns)
        print(f"Graph.funOf: +{len(paths)} → funOf.lean")
    if more:
        paths, rns = rebuild_parent(graph, "funOf", more, as_more=True)
        for p in paths:
            deleted[f"{mod_g}.{p.stem}"] = f"{mod_g}.funOf_more"
        renames.extend(rns)
        print(f"Graph.funOf: +{len(paths)} → funOf_more.lean")
        # Drop Lambda Pref-bloat imports that cycle through funOf
        more_path = graph / "funOf_more.lean"
        keep_prefixes = (
            "Mathlib.",
            "DomainTheory.DataTypesAsLattices.Graph.",
            "DomainTheory.DataTypesAsLattices.Pomega.",
            "DomainTheory.DataTypesAsLattices.Continuous.",
            "DomainTheory.DataTypesAsLattices.FixedPoint.",
        )
        out: list[str] = []
        for line in more_path.read_text().splitlines(keepends=True):
            m = IMP_RE.match(line.rstrip("\n"))
            if m:
                mod = m.group("mod")
                if mod.endswith(".funOf") or any(mod.startswith(p) for p in keep_prefixes):
                    out.append(line)
                continue
            out.append(line)
        more_path.write_text("".join(out))
    return deleted, renames


def same_dir_import_graph(dirpath: Path) -> dict[str, list[str]]:
    prefix = f"DomainTheory.DataTypesAsLattices.{dirpath.name}."
    g: dict[str, list[str]] = {}
    for p in dirpath.glob("*.lean"):
        imps: list[str] = []
        for mod in parse_imports(p.read_text()):
            if mod.startswith(prefix):
                imps.append(mod[len(prefix) :])
        g[p.stem] = imps
    return g


def reaches(graph: dict[str, list[str]], start: str, target: str, remap: dict[str, str]) -> bool:
    seen: set[str] = set()
    stack = [remap.get(start, start)]
    while stack:
        u = stack.pop()
        u = remap.get(u, u)
        if u in seen:
            continue
        seen.add(u)
        if u == target:
            return True
        for v in graph.get(u, []):
            stack.append(remap.get(v, v))
    return False


def companion_needs_more(
    dirpath: Path,
    pref: str,
    stem: str,
    batch_stems: set[str],
    graph: dict[str, list[str]],
) -> bool:
    """True if merging this companion into pref would create an import cycle."""
    remap = {s: pref for s in batch_stems}
    remap[stem] = pref
    for imp in graph.get(stem, []):
        if imp == pref or imp in batch_stems:
            continue
        # After merge, pref imports `imp`. Cycle if imp can reach pref.
        if reaches(graph, imp, pref, remap):
            return True
    return False


def process_dir(name: str) -> tuple[dict[str, str], list[tuple[str, str]]]:
    dirpath = DTAL / name
    pairs = companion_pairs(dirpath)
    if not pairs:
        print(f"{name}: nothing to fold")
        return {}, []

    by_parent: dict[str, list[tuple[str, str]]] = defaultdict(list)
    for stem, parent, suffix in pairs:
        by_parent[parent].append((stem, suffix))

    companion_stems = {stem for stem, _, _ in pairs}

    def depth(p: str) -> tuple:
        return (1 if p in companion_stems else 0, p.count("_"), len(p))

    parents_ordered = sorted(by_parent.keys(), key=depth, reverse=True)

    deleted: dict[str, str] = {}
    renames: list[tuple[str, str]] = []
    mod_prefix = f"DomainTheory.DataTypesAsLattices.{name}"
    graph = same_dir_import_graph(dirpath)

    for pref in parents_ordered:
        kids = [(s, suf) for s, suf in by_parent[pref] if (dirpath / f"{s}.lean").exists()]
        if not kids or not (dirpath / f"{pref}.lean").exists():
            continue
        batch = {s for s, _ in kids}
        safe: list[tuple[str, str]] = []
        more: list[tuple[str, str]] = []
        for s, suf in kids:
            if companion_needs_more(dirpath, pref, s, batch, graph):
                more.append((s, suf))
            else:
                safe.append((s, suf))
        if safe:
            paths, rns = rebuild_parent(dirpath, pref, safe, as_more=False)
            for p in paths:
                deleted[f"{mod_prefix}.{p.stem}"] = f"{mod_prefix}.{pref}"
            renames.extend(rns)
            print(f"  {pref}: +{len(paths)} → {pref}.lean")
            # refresh graph edges: parent gains kids' imports
            graph = same_dir_import_graph(dirpath)
        if more:
            paths, rns = rebuild_parent(dirpath, pref, more, as_more=True)
            for p in paths:
                deleted[f"{mod_prefix}.{p.stem}"] = f"{mod_prefix}.{pref}_more"
            renames.extend(rns)
            print(f"  {pref}: +{len(paths)} → {pref}_more.lean (cycle)")
            graph = same_dir_import_graph(dirpath)

    return deleted, renames


def main() -> None:
    dirs = sys.argv[1:] if len(sys.argv) > 1 else DIRS
    all_deleted: dict[str, str] = {}
    all_renames: list[tuple[str, str]] = []

    # Special-case funOf first so Lambda orphans are gone before Lambda inventory
    if "Graph" in dirs or "Lambda" in dirs:
        d, r = fold_lambda_funof_into_graph()
        all_deleted.update(d)
        all_renames.extend(r)

    for name in dirs:
        print(f"\n=== {name} ===")
        d, r = process_dir(name)
        all_deleted.update(d)
        all_renames.extend(r)

    n = rewrite_imports_and_refs(all_deleted, all_renames)
    print(f"\nrewrote {n} files; deleted {len(all_deleted)} modules")

    # Drop deleted from DomainTheory.lean; ensure parent / _more imports remain
    dt_path = ROOT / "DomainTheory.lean"
    dt = dt_path.read_text()
    parents_needed: set[str] = set()
    for mod in sorted(all_deleted, key=len, reverse=True):
        dt = re.sub(rf"^import\s+{re.escape(mod)}\s*\n", "", dt, flags=re.M)
        parents_needed.add(all_deleted[mod])
    for parent in sorted(parents_needed):
        if f"import {parent}\n" not in dt and f"public import {parent}\n" not in dt:
            # insert after nearest sibling import sharing the package prefix
            pkg = parent.rsplit(".", 1)[0]
            anchor = None
            for line in dt.splitlines():
                if line.startswith("import " + pkg + "."):
                    anchor = line
            if anchor:
                dt = dt.replace(anchor + "\n", anchor + "\n" + f"import {parent}\n", 1)
            else:
                dt += f"\nimport {parent}\n"
    dt_path.write_text(dt)

    # Report leftovers
    for name in dirs:
        left = companion_pairs(DTAL / name)
        if left:
            print(f"LEFTOVER {name}: {len(left)}")
            for stem, parent, suf in left[:20]:
                print(f"  {stem} → {parent}.{suf}")


if __name__ == "__main__":
    main()
