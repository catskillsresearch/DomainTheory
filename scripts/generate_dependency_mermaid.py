#!/usr/bin/env python3
"""Regenerate DomainTheory *.mermaid dependency diagrams from Lean imports."""

from __future__ import annotations

import argparse
import re
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DT = ROOT / "DomainTheory"

IMPORT = re.compile(
    r"^(?:public\s+|private\s+|meta\s+)?import\s+(?:all\s+)?(\S+)\s*$"
)
BULLET_MD = re.compile(r"^\s*-\s+\[[^\]]*\]\(([^)]+)\)\s*$")
# Chapter indexes use ``0. [Title](path)``; section indexes use ``- [Title](path)``.
OUTLINE_LINK = re.compile(r"^\s*(?:-\s+|\d+\.\s+)\[[^\]]*\]\(([^)]+)\)\s*$")
OUTLINE_TITLE = re.compile(r"^\s*(?:-\s+|\d+\.\s+)\[([^\]]*)\]")
DEPRECATED_MERMAID = DT / "1972_Continuous_lattices.mermaid"
CL1972_SECTION_MERMAIDS = frozenset(
    {
        "1972_2_Continuous_lattices.mermaid",
        "1972_Function_spaces.mermaid",
        "1972_4_Inverse_limits.mermaid",
    }
)
CL1972_MERMAID_SECTION: dict[str, str] = {
    "1972_2_Continuous_lattices.mermaid": "CL",
    "1972_Function_spaces.mermaid": "FS",
    "1972_4_Inverse_limits.mermaid": "LIM",
}
CL1972_SECTION_LABELS: dict[str, str] = {
    "INJ": "Injective spaces",
    "CL": "Continuous lattices",
    "FS": "Function spaces",
    "LIM": "Inverse limits",
}
MERMAID_IMPORT = re.compile(r'@import\s+"([^"]+\.mermaid)"')
LEAN_IMPORT = re.compile(r'@import\s+"([^"]+\.lean)"')
NODE_DEF = re.compile(r'^\s*(\w+)\["([^"]*)"\]\s*$')
NODE_SIMPLE = re.compile(r"^\s*(\w+)\s*-->\s*(\w+)\s*$")
NODE_LABELED = re.compile(r'^\s*(\w+)\s*-->\|"?(\d+)"?\|\s*(\w+)\s*$')
INIT_LINE = re.compile(r"^%%\{init:.*\}%%\s*$")

# Aggregator barrels (no declarations) — imports of these are skipped in note graphs when requested.
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom)\b"
)


def module_of(path: Path) -> str:
    rel = path.relative_to(ROOT)
    return ".".join(rel.with_suffix("").parts)


def path_of_module(mod: str) -> Path | None:
    if not mod.startswith("DomainTheory."):
        return None
    p = ROOT / Path(*mod.split(".")).with_suffix(".lean")
    return p if p.is_file() else None


def load_modules() -> dict[str, Path]:
    return {module_of(p): p for p in DT.rglob("*.lean")}


def is_aggregator(path: Path) -> bool:
    for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        if DECL.match(line.strip()):
            return False
    return True


def direct_imports_mod(mod: str, modules: dict[str, Path]) -> list[str]:
    path = modules.get(mod)
    if path is None:
        return []
    out: list[str] = []
    for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        m = IMPORT.match(line.strip())
        if m:
            out.append(m.group(1))
    return out


def find_index_md(mermaid: Path) -> Path | None:
    name = mermaid.name
    for md in list(DT.rglob("*.md")) + [ROOT / "DomainTheory.md"]:
        if not md.is_file():
            continue
        try:
            text = md.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        if f'@import "{name}"' in text:
            return md
    return None


def resolve_md(base: Path, href: str) -> Path | None:
    path = href.strip().split("#", 1)[0]
    if not path.endswith(".md"):
        return None
    target = (base.parent / path).resolve()
    return target if target.is_file() else None


def resolve_lean_href(base: Path, href: str) -> Path | None:
    path = href.strip().split("#", 1)[0]
    if not path.endswith(".lean"):
        return None
    target = (base.parent / path).resolve()
    if target.is_file():
        return target
    rooted = (ROOT / path).resolve()
    return rooted if rooted.is_file() else None


def lean_modules_from_note(md: Path) -> set[str]:
    text = md.read_text(encoding="utf-8", errors="ignore")
    mods: set[str] = set()
    for m in LEAN_IMPORT.finditer(text):
        p = resolve_lean_href(md, m.group(1))
        if p and p.is_relative_to(DT):
            mods.add(module_of(p))
    return mods


def modules_from_section_outline(md: Path) -> set[str]:
    """Lean modules for a section index whose children are linked outline notes."""
    mods: set[str] = set()
    for line in md.read_text(encoding="utf-8", errors="ignore").splitlines():
        m = OUTLINE_LINK.match(line)
        if not m:
            continue
        child = resolve_md(md, m.group(1))
        if child is None:
            continue
        mods |= note_module_set(child)
    return mods


def note_module_set(md: Path) -> set[str]:
    """Modules belonging to one outline box (note or whole topic folder)."""
    text = md.read_text(encoding="utf-8", errors="ignore")
    if re.search(r'@import\s+"[^"]+\.mermaid"', text):
        if md.parent.resolve() == DT.resolve():
            return modules_from_section_outline(md)
        folder = md.parent
        return {module_of(p) for p in folder.rglob("*.lean") if p.is_file()}
    return lean_modules_from_note(md)


def chapter_prefix(scope_dir: Path) -> tuple[str, ...]:
    rel = scope_dir.relative_to(DT)
    return tuple(rel.parts)


def resolve_to_node(
    imp_mod: str,
    scope_dir: Path,
    modules: dict[str, Path],
) -> str | None:
    if not imp_mod.startswith("DomainTheory."):
        return None
    imp_path = path_of_module(imp_mod)
    if imp_path is None:
        return None
    try:
        rel = imp_path.relative_to(DT)
    except ValueError:
        return None

    scope_rel = scope_dir.relative_to(DT)
    common = 0
    while (
        common < len(scope_rel.parts)
        and common < len(rel.parts)
        and scope_rel.parts[common] == rel.parts[common]
    ):
        common += 1

    if common == len(scope_rel.parts):
        rest = rel.parts[common:]
        if not rest:
            return None
        if len(rest) == 1:
            return Path(rest[0]).stem
        sub = scope_dir / rest[0]
        if sub.is_dir():
            return rest[0]
        return Path(rest[-1]).stem

    if scope_rel.parts and rel.parts[0] == scope_rel.parts[0]:
        return rel.parts[common]

    return rel.parts[0]


def transitive_reduce(pairs: set[tuple[str, str]]) -> set[tuple[str, str]]:
    """Remove edge u->v if another directed path u=>v exists (u != v)."""
    nodes = {a for a, _ in pairs} | {b for _, b in pairs}
    adj: dict[str, set[str]] = defaultdict(set)
    for a, b in pairs:
        adj[a].add(b)

    def reachable(src: str, dst: str, skip_direct: bool) -> bool:
        seen = {src}
        stack = list(adj[src])
        if skip_direct and dst in stack:
            stack = [x for x in stack if x != dst]
        while stack:
            n = stack.pop()
            if n == dst:
                return True
            if n in seen:
                continue
            seen.add(n)
            stack.extend(adj[n])
        return False

    out: set[tuple[str, str]] = set()
    for u, v in sorted(pairs):
        if reachable(u, v, skip_direct=True):
            continue
        out.add((u, v))
    return out


def parse_preserve_tail(old: str) -> tuple[list[str], dict[str, str], list[str]]:
    """Return (header_lines, node_labels, style_tail: classDef + class + init)."""
    lines = old.splitlines()
    header: list[str] = []
    labels: dict[str, str] = {}
    style: list[str] = []
    in_flow = False
    for line in lines:
        if line.startswith("%%") and not INIT_LINE.match(line):
            if not in_flow:
                header.append(line)
            continue
        if INIT_LINE.match(line):
            style.append(line)
            continue
        if line.startswith("flowchart"):
            in_flow = True
            continue
        if not in_flow:
            continue
        m = NODE_DEF.match(line)
        if m:
            labels[m.group(1)] = m.group(2)
            continue
        if line.strip().startswith("classDef ") or line.strip().startswith("class "):
            style.append(line)
    return header, labels, style


def mermaid_id(label: str, used: set[str]) -> str:
    base = re.sub(r"[^A-Za-z0-9_]", "_", label.strip())
    base = base.strip("_") or "N"
    if base[0].isdigit():
        base = "N_" + base
    cand = base
    i = 0
    while cand in used:
        i += 1
        cand = f"{base}_{i}"
    used.add(cand)
    return cand


def filter_style(style_tail: list[str], node_labels: dict[str, str]) -> list[str]:
    nodes = set(node_labels)
    out: list[str] = []
    for line in style_tail:
        st = line.strip()
        if st.startswith("classDef "):
            out.append(line)
            continue
        if st.startswith("class "):
            rest = st[len("class ") :]
            ids = [x.strip() for x in rest.split(",")]
            cls = ids[-1] if ids else ""
            nids = ids[:-1] if len(ids) > 1 else []
            kept = [n for n in nids if n in nodes]
            if kept:
                out.append(f"  class {','.join(kept + [cls])}")
            continue
        out.append(line)
    return out


def emit_flowchart(
    header: list[str],
    node_labels: dict[str, str],
    edges: dict[tuple[str, str], int],
    style_tail: list[str],
    *,
    labeled: bool,
    flowchart: str = "flowchart TB",
) -> str:
    style_tail = filter_style(style_tail, node_labels)
    out: list[str] = []
    out.extend(header)
    if not header or header[-1].strip():
        pass
    out.append(flowchart)
    out.append("")
    for nid in sorted(node_labels.keys(), key=lambda k: (node_labels[k].lower(), k)):
        lab = node_labels[nid].replace('"', "#quot;")
        out.append(f'  {nid}["{lab}"]')
    out.append("")
    for (src, dst) in sorted(edges.keys(), key=lambda e: (e[1], e[0])):
        c = edges[(src, dst)]
        if labeled:
            out.append(f'  {src} -->|"{c}"| {dst}')
        else:
            out.append(f"  {src} --> {dst}")
    if style_tail:
        out.append("")
        out.extend(style_tail)
    return "\n".join(out).rstrip() + "\n"


def gen_inside(mermaid: Path, modules: dict[str, Path], old: str) -> str:
    scope_dir = mermaid.parent
    inside_m = re.search(r"Inside (\w+)", old)
    folder_name = inside_m.group(1) if inside_m else scope_dir.name
    header = [
        f"%% Inside {folder_name}. A box is one Lean file in this folder, or one subfolder.",
        "%% A box named as another folder is that whole folder. A box named as another chapter is that whole chapter.",
        "%% The arrowhead points at the file or folder that imports. The label is how many direct imports.",
    ]
    _, old_labels, style = parse_preserve_tail(old)
    if not style:
        style = [
            "",
            "  classDef file fill:#dbeafe,stroke:#1d4ed8,color:#1e3a8a",
            "  classDef ext fill:#f3f4f6,stroke:#374151,color:#111827",
        ]

    internal: set[str] = set()
    for p in scope_dir.glob("*.lean"):
        internal.add(p.stem)
    for sub in scope_dir.iterdir():
        if sub.is_dir() and any(sub.rglob("*.lean")):
            internal.add(sub.name)

    node_labels: dict[str, str] = {}
    used_ids: set[str] = set()
    ext_nodes: set[str] = set()
    edges: dict[tuple[str, str], int] = defaultdict(int)
    name_to_nid: dict[str, str] = {}

    def nid_for(name: str, *, ext: bool) -> str:
        if name in name_to_nid:
            return name_to_nid[name]
        for oid, lab in old_labels.items():
            plain = lab.split("<br>")[0].strip()
            if plain == name or lab == name:
                name_to_nid[name] = oid
                used_ids.add(oid)
                node_labels[oid] = lab
                if ext:
                    ext_nodes.add(oid)
                return oid
        nid = mermaid_id(name, used_ids)
        name_to_nid[name] = nid
        node_labels[nid] = name
        if ext:
            ext_nodes.add(nid)
        return nid

    for p in sorted(scope_dir.glob("*.lean")):
        mod = module_of(p)
        importer = p.stem
        dst = nid_for(importer, ext=False)
        for imp in direct_imports_mod(mod, modules):
            node = resolve_to_node(imp, scope_dir, modules)
            if node is None or node == importer:
                continue
            ext = node not in internal
            src = nid_for(node, ext=ext)
            edges[(src, dst)] += 1

    # class lines
    class_lines = [ln for ln in style if ln.strip().startswith("classDef ")]
    if not class_lines:
        class_lines = [
            "  classDef file fill:#dbeafe,stroke:#1d4ed8,color:#1e3a8a",
            "  classDef ext fill:#f3f4f6,stroke:#374151,color:#111827",
        ]
    assign = []
    for nid in sorted(node_labels.keys()):
        if any(ln.strip() == f"class {nid} ext" for ln in style):
            assign.append(f"  class {nid} ext")
        elif any(ln.strip() == f"class {nid} file" for ln in style):
            assign.append(f"  class {nid} file")
        elif nid in ext_nodes:
            assign.append(f"  class {nid} ext")
        else:
            assign.append(f"  class {nid} file")
    style_out = [ln for ln in style if ln.strip().startswith("%%{init")] + class_lines + assign

    return emit_flowchart(header, node_labels, edges, style_out, labeled=True)


def gen_folder_aggregate(
    mermaid: Path,
    modules: dict[str, Path],
    old: str,
    *,
    parent_dir: Path,
    include_root_lean: bool = False,
) -> str:
    header, old_labels, style = parse_preserve_tail(old)
    if not header:
        header = [
            "%% Each box is one folder.",
            "%% The arrowhead points at the folder that imports. The label is how many direct imports.",
        ]

    folders: list[tuple[str, Path]] = []
    for sub in sorted(parent_dir.iterdir()):
        if sub.is_dir() and any(sub.rglob("*.lean")):
            folders.append((sub.name, sub))
    if include_root_lean and any(parent_dir.glob("*.lean")):
        folders.append((parent_dir.name, parent_dir))

    folder_mods: dict[str, set[str]] = {}
    for name, folder in folders:
        if folder == parent_dir:
            folder_mods[name] = {
                module_of(p) for p in parent_dir.glob("*.lean") if p.is_file()
            }
        else:
            folder_mods[name] = {module_of(p) for p in folder.rglob("*.lean")}

    node_labels: dict[str, str] = {}
    name_to_nid: dict[str, str] = {}
    used: set[str] = set()
    for i, (name, _) in enumerate(folders):
        nid = f"N{i}"
        if name in old_labels.values():
            for k, v in old_labels.items():
                if v == name:
                    nid = k
                    break
        used.add(nid)
        name_to_nid[name] = nid
        node_labels[nid] = old_labels.get(nid, name)

    edges: dict[tuple[str, str], int] = defaultdict(int)
    for dst_name, dst_mods in folder_mods.items():
        dst_nid = name_to_nid[dst_name]
        for mod in dst_mods:
            for imp in direct_imports_mod(mod, modules):
                imp_path = path_of_module(imp)
                if imp_path is None:
                    continue
                for src_name, src_mods in folder_mods.items():
                    if imp in src_mods:
                        edges[(name_to_nid[src_name], dst_nid)] += 1
                        break

    return emit_flowchart(header, node_labels, edges, style, labeled=True)


def gen_note_outline(
    mermaid: Path,
    modules: dict[str, Path],
    old: str,
    *,
    skip_aggregators: bool = False,
    reduce: bool = True,
    labeled: bool = True,
    box_modules_fn=None,
    extra_title_ids: dict[str, str] | None = None,
    external_sections: dict[str, tuple[str, set[str]]] | None = None,
    header_lines: list[str] | None = None,
) -> str:
    header, old_labels, style = parse_preserve_tail(old)
    if header_lines is not None:
        header = header_lines
    elif external_sections:
        header = [
            "%% Outline notes in this section; INJ/CL/FS/LIM are other 1972 chapter sections.",
            "%% Arrowhead on the importer. The number is a direct-import count.",
            "%% An arrow already implied by a longer path is omitted.",
        ]
    index_md = find_index_md(mermaid)
    if index_md is None:
        raise ValueError(f"no index md for {mermaid}")

    boxes: list[tuple[str, set[str]]] = []
    for line in index_md.read_text(encoding="utf-8", errors="ignore").splitlines():
        m = OUTLINE_LINK.match(line)
        if not m:
            continue
        child = resolve_md(index_md, m.group(1))
        if child is None:
            continue
        title_m = OUTLINE_TITLE.match(line)
        title = title_m.group(1) if title_m else child.stem
        if re.search(r"(?i)^introduction$", title.strip(), re.I) and not lean_modules_from_note(child):
            continue
        if box_modules_fn is not None:
            mods = box_modules_fn(child, title)
        else:
            mods = note_module_set(child)
        if not mods:
            continue
        boxes.append((title, mods))

    # node ids from old labels order or titles
    node_labels: dict[str, str] = {}
    title_to_nid: dict[str, str] = {}
    mod_to_nid: dict[str, str] = {}
    used: set[str] = set()

    def title_id(title: str) -> str:
        mapping = dict(extra_title_ids or {})
        mapping.update({
            "Continuous functions": "CONT",
            "Computability and definability": "COMP",
            "Retracts and data types": "RET",
            "Closure operations and algebraic lattices": "CLO",
            "Subsets and their classification": "CLASS",
            "Total functions and functionality": "FUN",
            "Enumeration and degrees": "ENUM",
            "Introduction": "INTRO",
            "Injective spaces": "INJ",
            "Continuous lattices": "CL",
            "Function spaces": "FS",
            "Inverse limits": "LIM",
            "0. Introduction": "INTRO",
            "1. Injective spaces": "INJ",
            "2. Continuous lattices": "CL",
            "3. Function spaces": "FS",
            "4. Inverse limits": "LIM",
            "e": "E",
            "pair": "PAIR",
            "Continuous": "CONT",
            "Graph": "GRA",
            "FixedPoint": "FIX",
            "Embedding": "EMB",
        })
        if title in mapping:
            return mapping[title]
        tnorm = title.strip().lower()
        for oid, lab in old_labels.items():
            plain = lab.replace("<br>", " ").replace("\\n", " ").strip().lower()
            head = plain.split("—")[0].strip()
            if plain == tnorm or head == tnorm:
                return oid
        return mermaid_id(title[:24], used)

    for title, mods in boxes:
        nid = title_id(title)
        used.add(nid)
        title_to_nid[title] = nid
        node_labels[nid] = old_labels.get(nid, title)
        for mod in mods:
            # First outline note in paper order owns a shared @import (e.g. InjectiveSpace.lean).
            mod_to_nid.setdefault(mod, nid)

    if external_sections:
        for sec_id, (sec_title, _sec_mods) in external_sections.items():
            used.add(sec_id)
            node_labels[sec_id] = old_labels.get(sec_id, sec_title)

    edges: dict[tuple[str, str], int] = defaultdict(int)
    for _title, dst_mods in boxes:
        dst_nid = title_to_nid[_title]
        for mod in dst_mods:
            for imp in direct_imports_mod(mod, modules):
                if skip_aggregators:
                    ip = path_of_module(imp)
                    if ip and is_aggregator(ip):
                        continue
                src_nid = mod_to_nid.get(imp)
                if src_nid is None and external_sections:
                    for sec_id in CL1972_SECTION_LABELS:
                        if sec_id not in external_sections:
                            continue
                        if imp in external_sections[sec_id][1]:
                            src_nid = sec_id
                            break
                if src_nid is None:
                    continue
                if src_nid == dst_nid:
                    continue
                edges[(src_nid, dst_nid)] += 1

    if reduce:
        external_ids = set(external_sections or {})
        internal_ids = {nid for nid in node_labels if nid not in external_ids}
        internal_pairs = {
            (a, b) for (a, b), c in edges.items() if c > 0 and a in internal_ids and b in internal_ids
        }
        kept = transitive_reduce(internal_pairs)
        reduced: dict[tuple[str, str], int] = {
            (a, b): edges[(a, b)] for a, b in kept
        }
        for (a, b), c in edges.items():
            if c <= 0:
                continue
            if a in external_ids or b in external_ids:
                reduced[(a, b)] = c
        edges = reduced

    return emit_flowchart(header, node_labels, edges, style, labeled=labeled)


def gen_neighborhood_items(mermaid: Path, modules: dict[str, Path], old: str) -> str:
    header, old_labels, style = parse_preserve_tail(old)
    scope_dir = mermaid.parent
    index_md = find_index_md(mermaid)
    if index_md is None:
        raise ValueError(f"no index md for {mermaid}")

    stem_to_nid: dict[str, str] = {}
    node_labels: dict[str, str] = {}
    for line in index_md.read_text(encoding="utf-8", errors="ignore").splitlines():
        m = BULLET_MD.match(line)
        if not m:
            continue
        child = resolve_md(index_md, m.group(1))
        if child is None:
            continue
        if re.search(r"(?i)introduction", child.read_text(encoding="utf-8", errors="ignore")[:200]):
            if not lean_modules_from_note(child):
                continue
        for mod in lean_modules_from_note(child):
            stem = path_of_module(mod).stem if path_of_module(mod) else mod.split(".")[-1]
            if stem in stem_to_nid:
                continue
            nid = stem
            if nid not in old_labels:
                nid = mermaid_id(stem, set(stem_to_nid.values()))
            stem_to_nid[stem] = nid
            if mod not in stem_to_nid:
                pass
            node_labels[nid] = old_labels.get(nid, stem)

    # also all lean files in folder
    for p in scope_dir.glob("*.lean"):
        stem = p.stem
        if stem not in stem_to_nid:
            nid = stem if stem in old_labels else mermaid_id(stem, set(stem_to_nid.values()))
            stem_to_nid[stem] = nid
            node_labels[nid] = old_labels.get(nid, stem)

    mod_to_nid: dict[str, str] = {}
    for stem, nid in stem_to_nid.items():
        for p in scope_dir.glob("*.lean"):
            if p.stem == stem:
                mod_to_nid[module_of(p)] = nid

    pairs: set[tuple[str, str]] = set()
    for p in scope_dir.glob("*.lean"):
        mod = module_of(p)
        dst = mod_to_nid.get(mod)
        if dst is None:
            continue
        for imp in direct_imports_mod(mod, modules):
            imp_p = path_of_module(imp)
            if imp_p is None or imp_p.parent != scope_dir:
                continue
            src = mod_to_nid.get(imp)
            if src and src != dst:
                pairs.add((src, dst))

    kept = transitive_reduce(pairs)
    edges = {(a, b): 1 for a, b in kept}

    init = [ln for ln in style if INIT_LINE.match(ln.strip())]
    rest_style = [ln for ln in style if ln.strip().startswith("classDef ") or ln.strip().startswith("class ")]
    return emit_flowchart(
        header,
        node_labels,
        edges,
        init + rest_style,
        labeled=False,
        flowchart="flowchart TB",
    )


def gen_top_chapters(mermaid: Path, modules: dict[str, Path], old: str) -> str:
    header = [
        "%% Each box is one chapter on the top page.",
        "%% The arrowhead is on the chapter that imports. The number is a direct-import count.",
        "%% Datatypes as lattices and the references have no Lean imports across these chapters.",
    ]
    _, _, style = parse_preserve_tail(old)
    chapters = {
        "CL": ("ContinuousLattice", {module_of(p) for p in (DT / "ContinuousLattice").rglob("*.lean")}),
        "DT": ("DataTypesAsLattices", {module_of(p) for p in (DT / "DataTypesAsLattices").rglob("*.lean")}),
        "NS": ("NeighbourhoodSystems", {module_of(p) for p in (DT / "NeighbourhoodSystems").rglob("*.lean")}),
        "IS": ("InformationSystems", {module_of(p) for p in (DT / "InformationSystems").rglob("*.lean")}),
        "BR": ("BridgeTheorems", {module_of(p) for p in (DT / "BridgeTheorems").rglob("*.lean")}),
    }
    node_labels = {
        "CL": "Continuous Lattices\\n1972",
        "DT": "Datatypes as Lattices\\n1976",
        "NS": "Neighborhood Systems\\n1980",
        "IS": "Information Systems\\n1982",
        "BR": "Bridge Theorems",
    }
    ch_mods = {k: v[1] for k, v in chapters.items()}
    edges: dict[tuple[str, str], int] = defaultdict(int)
    for dst_key, dst_mods in ch_mods.items():
        if dst_key != "BR":
            continue
        for mod in dst_mods:
            for imp in direct_imports_mod(mod, modules):
                for src_key, src_mods in ch_mods.items():
                    if imp in src_mods:
                        edges[(src_key, dst_key)] += 1
                        break
    return emit_flowchart(header, node_labels, edges, style, labeled=True)


def cl1972_outline_box_modules(child: Path, title: str) -> set[str]:
    if re.match(r"(?i)introduction\s*$", title.strip()):
        return set()
    text = child.read_text(encoding="utf-8", errors="ignore")
    if any(OUTLINE_LINK.match(ln) for ln in text.splitlines()):
        return modules_from_section_outline(child)
    return lean_modules_from_note(child)


def cl1972_chapter_section_modules() -> dict[str, set[str]]:
    """Lean modules owned by each numbered section of the 1972 chapter (by outline tree)."""
    index_paths = {
        "INJ": DT / "ContinuousLattice" / "Injective" / "1972_Injective_spaces.md",
        "CL": DT / "ContinuousLattice" / "1972_2_Continuous_lattices.md",
        "FS": DT / "ContinuousLattice" / "1972_3_Function_spaces.md",
        "LIM": DT / "ContinuousLattice" / "1972_4_Inverse_limits.md",
    }
    out: dict[str, set[str]] = {}
    for sec_id, md in index_paths.items():
        if md.is_file():
            out[sec_id] = modules_from_section_outline(md)
    return out


def cl1972_external_sections(for_section: str) -> dict[str, tuple[str, set[str]]]:
    """Other chapter sections as importer sources (title, module set)."""
    all_mods = cl1972_chapter_section_modules()
    return {
        sec_id: (CL1972_SECTION_LABELS[sec_id], all_mods[sec_id])
        for sec_id in all_mods
        if sec_id != for_section
    }


def classify(mermaid: Path, text: str) -> str:
    if mermaid.name in CL1972_SECTION_MERMAIDS:
        return "cl1972_section"
    if mermaid.name == "1972_ContinuousLattices.mermaid":
        return "cl1972_chapter"
    if mermaid.name == "DomainTheory.mermaid":
        return "top_chapters"
    if mermaid.name == "Specialization.mermaid" and mermaid.parent.name == "Specialization":
        return "note_outline"
    if "Inside " in text.split("flowchart")[0]:
        return "inside"
    if "Lean files imported under this note" in text.split("flowchart")[0]:
        return "inside"
    if "Each box is one folder under BridgeTheorems" in text:
        return "bridge_folders"
    if "Each box is one folder under InformationSystems" in text:
        return "info_folders"
    if "Each box is one section" in text and "1980_Neighborhood" in mermaid.name:
        return "ns_sections"
    if "Each box is one item" in text:
        return "ns_items"
    if "Continuous functions on Pω" in text:
        return "note_outline"
    if (
        "Each box is a note" in text
        or "Each box is one outline note" in text
        or "Each box is one construction" in text
    ):
        return "note_outline"
    if "Each box is a section" in text or "Data types as lattices" in text:
        return "note_outline"
    if "The inverse system" in text:
        return "note_outline"
    if "Notes of section" in text or "Notes of the" in text or "The proof that" in text:
        return "note_outline"
    if "Each box is one section" in text:
        return "note_outline"
    if "Arrowhead on the importer" in text and "Section 0" in text:
        return "note_outline"
    if "projection induced" in text or "function space tower" in text.lower():
        return "note_outline"
    return "unknown"


def regenerate_one(mermaid: Path, modules: dict[str, Path]) -> str | None:
    old = mermaid.read_text(encoding="utf-8", errors="ignore")
    kind = classify(mermaid, old)
    if kind == "inside":
        return gen_inside(mermaid, modules, old)
    if kind == "bridge_folders":
        return gen_folder_aggregate(
            mermaid, modules, old, parent_dir=DT / "BridgeTheorems", include_root_lean=True
        )
    if kind == "info_folders":
        return gen_folder_aggregate(mermaid, modules, old, parent_dir=DT / "InformationSystems")
    if kind == "top_chapters":
        return gen_top_chapters(mermaid, modules, old)
    if kind == "cl1972_section":
        sec_id = CL1972_MERMAID_SECTION[mermaid.name]
        style = list(parse_preserve_tail(old)[2])
        if not any("classDef section" in s for s in style):
            style.extend(
                [
                    "  classDef section fill:#dbeafe,stroke:#1d4ed8,color:#1e3a8a",
                ]
            )
        external = cl1972_external_sections(sec_id)
        text = gen_note_outline(
            mermaid,
            modules,
            old,
            reduce=True,
            labeled=True,
            box_modules_fn=cl1972_outline_box_modules,
            external_sections=external,
        )
        # Style sibling section boxes like the chapter diagram.
        ext_ids = ",".join(sorted(external))
        if ext_ids and "classDef section" in text:
            text = text.rstrip() + f"\n  class {ext_ids},section\n"
        return text
    if kind == "cl1972_chapter":
        cl_ids = {
            "Injective spaces": "INJ",
            "Continuous lattices": "CL",
            "Function spaces": "FS",
            "Inverse limits": "LIM",
            "Correction": "COR",
        }
        return gen_note_outline(
            mermaid,
            modules,
            old,
            reduce=False,
            labeled=True,
            box_modules_fn=cl1972_outline_box_modules,
            extra_title_ids=cl_ids,
            header_lines=[
                "%% Each box is one section from 1972_ContinuousLattices.md (Introduction omitted).",
                "%% Arrowhead on the importer. The number is a direct-import count between sections.",
            ],
        )
    if kind == "ns_sections":
        ns_ids = {
            "Domains given by neighbourhoods": "DOM",
            "Mappings between domains": "MAP",
            "Domain constructs": "CON",
            "Fixed points and recursion": "FIX",
            "Typed $\\lambda$-calculus": "LAM",
            "Domain equations": "EQ",
            "Computability in effectively given domains": "COMP",
            "Retracts of the universal domain": "RET",
        }

        def ns_box_modules(child: Path, _title: str) -> set[str]:
            return {module_of(p) for p in child.parent.rglob("*.lean")}

        return gen_note_outline(
            mermaid,
            modules,
            old,
            reduce=True,
            labeled=True,
            box_modules_fn=ns_box_modules,
            extra_title_ids=ns_ids,
        )
    if kind == "ns_items":
        return gen_neighborhood_items(mermaid, modules, old)
    if kind == "note_outline":
        skip = "Imports of a folder barrel are not counted" in old
        reduce = "transitive" in old.lower() or "longer path" in old.lower()
        extra_ids: dict[str, str] | None = None
        header_lines: list[str] | None = None
        if mermaid.name == "Specialization.mermaid":
            reduce = True
            header_lines = [
                "%% Notes of the specialization order, in outline order.",
                "%% Each box is one outline note from 1972_Specialization_order.md.",
                "%% Arrowhead on the importer. The number is a direct-import count.",
                "%% An arrow already implied by a longer path is omitted.",
            ]
            extra_ids = {
                "MonotoneNet": "MN",
                "ScottConvergesTo": "SCT",
                "SpecializationLe": "SLe",
                "scottTopologicalSpace": "STS",
                "Scott open": "SO",
                "Proposition 2.1": "P21",
            }
        if mermaid.name == "Injective.mermaid":
            extra_ids = {
                "Definition 1.1: Injective Space": "D11",
                "Proposition 1.2": "P12",
                "Proposition 1.3": "P13",
                "Powers of 𝕆 are injective": "PO",
                "Proposition 1.4": "P14",
                "Proposition 1.5": "P15",
                "RetractSubspace": "IRS",
                "Corollary 1.6": "C16",
                "Corollary 1.7": "C17",
            }
        return gen_note_outline(
            mermaid,
            modules,
            old,
            skip_aggregators=skip,
            reduce=reduce,
            labeled=True,
            extra_title_ids=extra_ids,
            header_lines=header_lines,
        )
    return None


def remove_deprecated_mermaid() -> None:
    """Drop the ambiguous ``1972_Continuous_lattices`` file; use ``1972_ContinuousLattices``."""
    if not DEPRECATED_MERMAID.is_file():
        return
    for md in list(DT.rglob("*.md")) + [ROOT / "DomainTheory.md"]:
        if not md.is_file():
            continue
        text = md.read_text(encoding="utf-8", errors="ignore")
        if f'@import "{DEPRECATED_MERMAID.name}"' in text:
            raise SystemExit(
                f"{md.relative_to(ROOT)} still imports {DEPRECATED_MERMAID.name}; "
                f"use 1972_ContinuousLattices.mermaid (chapter) or "
                f"1972_2_Continuous_lattices.mermaid (section 2 notes)."
            )
    DEPRECATED_MERMAID.unlink()
    print(f"removed deprecated {DEPRECATED_MERMAID.relative_to(ROOT)}")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("paths", nargs="*", help="mermaid files (default: all under DomainTheory + DomainTheory.mermaid)")
    args = ap.parse_args()

    modules = load_modules()
    paths: list[Path] = []
    if args.paths:
        paths = [Path(p).resolve() for p in args.paths]
    else:
        paths = sorted(DT.rglob("*.mermaid"))
        top = ROOT / "DomainTheory.mermaid"
        if top.is_file():
            paths.append(top)

    changed = 0
    unknown: list[Path] = []
    for mermaid in paths:
        new = regenerate_one(mermaid, modules)
        if new is None:
            unknown.append(mermaid)
            continue
        old = mermaid.read_text(encoding="utf-8", errors="ignore")
        if new != old:
            changed += 1
            if args.write:
                mermaid.write_text(new, encoding="utf-8")
            elif not args.check:
                print(f"would update {mermaid.relative_to(ROOT)}")

    if args.check and changed:
        print(f"{changed} diagrams differ from generated")
        raise SystemExit(1)
    if args.write:
        print(f"updated {changed} diagrams")
        remove_deprecated_mermaid()
    if unknown:
        print("unknown kinds:", ", ".join(str(p.relative_to(ROOT)) for p in unknown))


if __name__ == "__main__":
    main()
