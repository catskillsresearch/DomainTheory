#!/usr/bin/env python3
"""Regenerate DomainTheory *.mermaid dependency diagrams from Lean imports."""

from __future__ import annotations

import argparse
import re
from collections import defaultdict
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parents[1]
DT = ROOT / "DomainTheory"

IMPORT = re.compile(
    r"^(?:public\s+|private\s+|meta\s+)?import\s+(?:all\s+)?(\S+)\s*$"
)
BULLET_MD = re.compile(r"^\s*-\s+\[[^\]]*\]\(([^)]+)\)\s*$")
# Chapter indexes use ``0. [Title](path)``; section indexes use ``- [Title](path)``.
# Non-greedy title (same as compile_md_tree TOC) so ``$[D \to D']$`` in link text parses.
OUTLINE_LINK = re.compile(
    r"^\s*(?:-\s+|\d+\.\s+)\[(?P<title>.+?)\]\((?P<href>[^)]+\.md)\)"
    r"(?:[ \t]+\[[^\]]*\]\([^)]*\))*"
    r"(?:[ \t]+✓)?[ \t]*$"
)
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


def transitive_import_closure(
    seeds: set[str],
    modules: dict[str, Path],
) -> set[str]:
    """All ``DomainTheory.*`` modules reachable from ``seeds`` via Lean ``import``."""
    if not seeds:
        return set()
    out = set(seeds)
    stack = list(seeds)
    while stack:
        mod = stack.pop()
        for imp in direct_imports_mod(mod, modules):
            if not imp.startswith("DomainTheory."):
                continue
            if imp not in modules:
                continue
            if imp not in out:
                out.add(imp)
                stack.append(imp)
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


def modules_from_section_outline(md: Path, modules: dict[str, Path] | None = None) -> set[str]:
    """Lean modules for a section index whose children are linked outline notes."""
    seeds: set[str] = set()
    for line in md.read_text(encoding="utf-8", errors="ignore").splitlines():
        m = OUTLINE_LINK.match(line)
        if not m:
            continue
        child = resolve_md(md, m.group("href"))
        if child is None:
            continue
        seeds |= note_module_set(child)
    if modules is not None:
        return transitive_import_closure(seeds, modules)
    return seeds


def note_module_set(md: Path) -> set[str]:
    """Modules belonging to one outline box (note or whole topic folder)."""
    text = md.read_text(encoding="utf-8", errors="ignore")
    if re.search(r'@import\s+"[^"]+\.mermaid"', text):
        if any(OUTLINE_LINK.match(ln) for ln in text.splitlines()):
            return modules_from_section_outline(md)
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


def mermaid_display_label(text: str) -> str:
    """Outline titles use $...$ for PDF math; Mermaid node labels do not render LaTeX."""
    s = re.sub(r"\$([^$]*)\$", r"\1", text)
    s = s.replace("$", "")
    s = re.sub(r"\*\*([^*]+)\*\*", r"\1", s)
    s = re.sub(r"\*([^*]+)\*", r"\1", s)
    s = s.replace(r"\mathbf{P}\omega", "Pω")
    s = re.sub(r"\\mathbf\{([^{}]+)\}", r"\1", s)
    for src, dst in (
        (r"\varnothing", "∅"),
        (r"\bot", "⊥"),
        (r"\top", "⊤"),
        (r"\omega", "ω"),
        (r"\lambda", "λ"),
        (r"\to", "→"),
        (r"\cap", "∩"),
        (r"\cup", "∪"),
        (r"\subseteq", "⊆"),
        (r"\in", "∈"),
        (r"\mathbb{N}", "ℕ"),
        (r"\leq", "≤"),
        (r"\geq", "≥"),
    ):
        s = s.replace(src, dst)
    return s


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
            # Mermaid: `class nodeId1,nodeId2 className` (space before class name).
            rest = st[len("class ") :]
            parts = rest.rsplit(None, 1)
            if len(parts) != 2:
                continue
            nids = [x.strip() for x in parts[0].split(",") if x.strip()]
            cls = parts[1].strip()
            kept = [n for n in nids if n in nodes]
            if kept:
                out.append(f"  class {','.join(kept)} {cls}")
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
    node_order: list[str] | None = None,
    subgraphs: list[tuple[str, list[str]]] | None = None,
    rank_same: list[list[str]] | None = None,
    subgraph_directions: dict[str, str] | None = None,
) -> str:
    style_tail = filter_style(style_tail, node_labels)

    def emit_node(nid: str, indent: str = "  ") -> None:
        lab = mermaid_display_label(node_labels[nid]).replace('"', "#quot;")
        out.append(f'{indent}{nid}["{lab}"]')

    if node_order is None:
        node_order = sorted(node_labels.keys(), key=lambda k: (node_labels[k].lower(), k))
    else:
        seen = set(node_order)
        node_order = list(node_order) + [n for n in node_labels if n not in seen]

    out: list[str] = []
    out.extend(header)
    out.append(flowchart)
    out.append("")

    placed: set[str] = set()
    subgraph_id_used: set[str] = set(node_labels.keys())
    if subgraphs:
        subgraph_member_nids: set[str] = set()
        for _sg_title, sg_nids in subgraphs:
            subgraph_member_nids.update(n for n in sg_nids if n in node_labels)
        for nid in node_order:
            if nid in node_labels and nid not in subgraph_member_nids:
                emit_node(nid)
                placed.add(nid)
        if placed:
            out.append("")
        for sg_title, sg_nids in subgraphs:
            members = [n for n in sg_nids if n in node_labels]
            if not members:
                continue
            safe = sg_title.replace('"', "#quot;")
            sid = mermaid_id(f"sg_{sg_title[:28]}", subgraph_id_used)
            out.append(f'  subgraph {sid}["{safe}"]')
            sg_dir = (subgraph_directions or {}).get(sg_title)
            if sg_dir:
                out.append(f"    direction {sg_dir}")
            for nid in members:
                emit_node(nid, indent="    ")
                placed.add(nid)
            out.append("  end")
        loose = [n for n in node_order if n not in placed and n in node_labels]
        if loose:
            out.append("")
            for nid in loose:
                emit_node(nid)
    else:
        for nid in node_order:
            emit_node(nid)

    if rank_same:
        out.append("")
        for group in rank_same:
            nids = [n for n in group if n in node_labels]
            if len(nids) >= 2:
                out.append(f"  {' ~~~ '.join(nids)}")

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


def outline_mermaid_header(index_md_name: str) -> list[str]:
    return [
        f"%% Each box is one outline note from {index_md_name}.",
        "%% Lean modules = transitive closure of that note's @import Lean files.",
        "%% Arrowhead on the importer. An arrow implied by a longer path is omitted.",
    ]


def gen_note_outline(
    mermaid: Path,
    modules: dict[str, Path],
    old: str,
    *,
    skip_aggregators: bool = False,
    reduce: bool = True,
    labeled: bool = False,
    box_modules_fn=None,
    extra_title_ids: dict[str, str] | None = None,
    external_sections: dict[str, tuple[str, set[str]]] | None = None,
    header_lines: list[str] | None = None,
    include_empty_outline_boxes: bool = False,
    mod_nid_override: Callable[[str, dict[str, str]], str | None] | None = None,
    edge_filter: Callable[[str, str], bool] | None = None,
    restore_orphans: bool = False,
    preserve_hub_titles: frozenset[str] | None = None,
    transitive_modules: bool = True,
    subgraph_groups: list[tuple[str, list[str]]] | None = None,
    rank_same_titles: list[list[str]] | None = None,
    subgraph_directions: dict[str, str] | None = None,
    flowchart: str = "flowchart TB",
    force_outline_edges: list[tuple[str, str]] | None = None,
    collapse_hub_into_subgraph: str | tuple[str, str] | None = None,
    exclude_outline_titles: frozenset[str] | None = None,
) -> str:
    header, old_labels, style = parse_preserve_tail(old)
    index_md = find_index_md(mermaid)
    if header_lines is not None:
        header = header_lines
    elif index_md is not None:
        header = outline_mermaid_header(index_md.name)
    elif external_sections:
        header = [
            "%% Outline notes in this section; INJ/CL/FS/LIM are other 1972 chapter sections.",
            "%% Arrowhead on the importer. The number is a direct-import count.",
            "%% An arrow already implied by a longer path is omitted.",
        ]
    if index_md is None:
        raise ValueError(f"no index md for {mermaid}")

    boxes: list[tuple[str, set[str]]] = []
    for line in index_md.read_text(encoding="utf-8", errors="ignore").splitlines():
        m = OUTLINE_LINK.match(line)
        if not m:
            continue
        child = resolve_md(index_md, m.group("href"))
        if child is None:
            continue
        title = m.group("title")
        if exclude_outline_titles and title in exclude_outline_titles:
            continue
        if (
            re.search(r"(?i)^introduction$", title.strip(), re.I)
            and not lean_modules_from_note(child)
            and not include_empty_outline_boxes
        ):
            continue
        if box_modules_fn is not None:
            mods = box_modules_fn(child, title)
        else:
            mods = note_module_set(child)
        if not mods and not include_empty_outline_boxes:
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
        owned = (
            transitive_import_closure(mods, modules) if transitive_modules else mods
        )
        for mod in owned:
            # First outline note in paper order owns a shared @import (e.g. InjectiveSpace.lean).
            mod_to_nid.setdefault(mod, nid)

    if mod_nid_override is not None:
        for mod in list(mod_to_nid):
            override = mod_nid_override(mod, title_to_nid)
            if override is not None:
                mod_to_nid[mod] = override

    if external_sections:
        for sec_id, (sec_title, _sec_mods) in external_sections.items():
            used.add(sec_id)
            node_labels[sec_id] = old_labels.get(sec_id, sec_title)

    edges: dict[tuple[str, str], int] = defaultdict(int)
    for _title, dst_mods in boxes:
        dst_nid = title_to_nid[_title]
        scan_mods = (
            transitive_import_closure(dst_mods, modules)
            if transitive_modules
            else dst_mods
        )
        for mod in scan_mods:
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
                        sec_mods = external_sections[sec_id][1]
                        if transitive_modules:
                            sec_mods = transitive_import_closure(sec_mods, modules)
                        if imp in sec_mods:
                            src_nid = sec_id
                            break
                if src_nid is None:
                    continue
                if src_nid == dst_nid:
                    continue
                edges[(src_nid, dst_nid)] += 1

    if force_outline_edges:
        for src_title, dst_title in force_outline_edges:
            a = title_to_nid.get(src_title)
            b = title_to_nid.get(dst_title)
            if a is not None and b is not None and a != b:
                edges[(a, b)] += 1

    if edge_filter is not None:
        nid_to_title = {v: k for k, v in title_to_nid.items()}
        edges = {
            (a, b): c
            for (a, b), c in edges.items()
            if edge_filter(nid_to_title[a], nid_to_title[b])
        }

    full_edges = dict(edges)

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

    if preserve_hub_titles is not None:
        nid_to_title = {v: k for k, v in title_to_nid.items()}
        title_to_nid_local = title_to_nid
        hub_nids = {
            title_to_nid_local[t]
            for t in preserve_hub_titles
            if t in title_to_nid_local
        }
        for (a, b), c in full_edges.items():
            if a in hub_nids and b in hub_nids:
                edges[(a, b)] = c

    if restore_orphans:
        internal_ids = {nid for nid in node_labels if nid not in set(external_sections or {})}
        edges = restore_orphan_outline_edges(full_edges, edges, internal_ids)

    outline_nids = [title_to_nid[t] for t, _ in boxes if t in title_to_nid]
    subgraphs: list[tuple[str, list[str]]] | None = None
    rank_same: list[list[str]] | None = None
    if subgraph_groups is not None:
        subgraphs = []
        for sg_title, titles in subgraph_groups:
            nids = [title_to_nid[t] for t in titles if t in title_to_nid]
            if nids:
                subgraphs.append((sg_title, nids))
    if rank_same_titles is not None:
        rank_same = [
            [title_to_nid[t] for t in group if t in title_to_nid]
            for group in rank_same_titles
        ]

    if collapse_hub_into_subgraph is not None and subgraph_groups is not None:
        if isinstance(collapse_hub_into_subgraph, tuple):
            hub_title, only_sg_title = collapse_hub_into_subgraph
            sg_filter = {only_sg_title}
        else:
            hub_title = collapse_hub_into_subgraph
            sg_filter = None
        hub_nid = title_to_nid.get(hub_title)
        if hub_nid is not None:
            sid_used: set[str] = set(node_labels) | set(title_to_nid.values())
            for sg_title, sg_member_titles in subgraph_groups:
                if sg_filter is not None and sg_title not in sg_filter:
                    continue
                sg_member_nids = {
                    title_to_nid[t] for t in sg_member_titles if t in title_to_nid
                }
                if not sg_member_nids:
                    continue
                sg_sid = mermaid_id(f"sg_{sg_title[:28]}", sid_used)
                sid_used.add(sg_sid)
                hub_to_members = [
                    (a, b)
                    for (a, b) in edges
                    if a == hub_nid and b in sg_member_nids
                ]
                if hub_to_members:
                    weight = max(
                        (edges[(a, b)] for a, b in hub_to_members),
                        default=1,
                    )
                    edges = {
                        (a, b): c
                        for (a, b), c in edges.items()
                        if not (a == hub_nid and b in sg_member_nids)
                    }
                    edges[(hub_nid, sg_sid)] = max(
                        edges.get((hub_nid, sg_sid), 0),
                        weight,
                    )

    return emit_flowchart(
        header,
        node_labels,
        edges,
        style,
        labeled=labeled,
        flowchart=flowchart,
        node_order=outline_nids,
        subgraphs=subgraphs,
        rank_same=rank_same,
        subgraph_directions=subgraph_directions,
    )


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


# 1976 Data types as lattices — section hubs vs the Lean folders they own.
# Continuous spans several topic folders; Computability sits under §2 definability;
# FixedLattices under §5 Closures. Paper-order forward edges only (later section imports
# earlier); reverse edges are implementation accidents and would cycle the reduce step.
DTAL_SECTION_ORDER: list[str] = [
    "CONT",
    "COMP",
    "ENUM",
    "RET",
    "CLO",
    "CLASS",
    "FUN",
]
DTAL_SECTION_LABELS: dict[str, str] = {
    "CONT": "Continuous functions",
    "COMP": "Computability and definability",
    "ENUM": "Enumeration and degrees",
    "RET": "Retracts and data types",
    "CLO": "Closure operations and algebraic lattices",
    "CLASS": "Subsets and their classification",
    "FUN": "Total functions and functionality",
}
DTAL_SECTION_FOLDERS: dict[str, tuple[str, ...]] = {
    "CONT": ("Pomega", "Continuous", "Graph", "FixedPoint", "Embedding"),
    "COMP": ("Lambda", "Computability"),
    "ENUM": ("Enumeration",),
    "RET": ("Retracts",),
    "CLO": ("Closures", "FixedLattices"),
    "CLASS": ("Classification",),
    "FUN": ("Functionality",),
}


def _gen_paper_section_deps(
    *,
    index_md_name: str,
    chapter_dir: Path,
    section_order: list[str],
    section_labels: dict[str, str],
    section_folders: dict[str, tuple[str, ...]],
    modules: dict[str, Path],
    old: str,
    default_class_defs: list[str] | None = None,
) -> str:
    """Folder-owned, paper-forward, labeled section dependency flowchart."""
    header = [
        f"%% Each box is one section from {index_md_name}.",
        "%% Lean modules = .lean files under that section's topic folders.",
        "%% Arrowhead on the importer; label = direct-import count.",
        "%% Only paper-forward edges (earlier → later). Paths implied by longer routes omitted.",
    ]
    _, old_labels, style = parse_preserve_tail(old)

    sec_mods: dict[str, set[str]] = {}
    mod_owner: dict[str, str] = {}
    for nid in section_order:
        mods: set[str] = set()
        for folder in section_folders[nid]:
            root = chapter_dir / folder
            if not root.is_dir():
                continue
            mods |= {module_of(p) for p in root.rglob("*.lean") if p.is_file()}
        sec_mods[nid] = mods
        for mod in mods:
            mod_owner[mod] = nid

    node_labels = {
        nid: old_labels.get(nid, section_labels[nid]) for nid in section_order
    }

    raw: dict[tuple[str, str], int] = defaultdict(int)
    for dst, mods in sec_mods.items():
        for mod in mods:
            for imp in direct_imports_mod(mod, modules):
                src = mod_owner.get(imp)
                if src is None or src == dst:
                    continue
                if section_order.index(src) >= section_order.index(dst):
                    continue
                raw[(src, dst)] += 1

    kept = transitive_reduce(set(raw))
    edges = {(a, b): raw[(a, b)] for a, b in kept}

    class_defs = [ln for ln in style if ln.strip().startswith("classDef ")]
    if not class_defs:
        class_defs = default_class_defs or [
            "  classDef c1 fill:#dcfce7,stroke:#15803d,color:#14532d",
            "  classDef c2 fill:#cffafe,stroke:#0e7490,color:#164e63",
            "  classDef c3 fill:#ffedd5,stroke:#c2410c,color:#7c2d12",
            "  classDef c4 fill:#ecfccb,stroke:#4d7c0f,color:#365314",
            "  classDef c5 fill:#f3e8ff,stroke:#7e22ce,color:#581c87",
            "  classDef c6 fill:#fde68a,stroke:#a16207,color:#713f12",
            "  classDef c7 fill:#e2e8f0,stroke:#334155,color:#0f172a",
            "  classDef c8 fill:#fae8ff,stroke:#a21caf,color:#701a75",
        ]
    class_assigns = [
        f"  class {nid} c{i}" for i, nid in enumerate(section_order, start=1)
    ]
    init = [ln for ln in style if INIT_LINE.match(ln.strip())]

    return emit_flowchart(
        header,
        node_labels,
        edges,
        init + class_defs + class_assigns,
        labeled=True,
        flowchart="flowchart TB",
        node_order=list(section_order),
    )


def gen_dtal_sections(mermaid: Path, modules: dict[str, Path], old: str) -> str:
    """Cross-section Lean deps for 1976_DataTypes.mermaid (folder ownership)."""
    return _gen_paper_section_deps(
        index_md_name="1976_DataTypes.md",
        chapter_dir=DT / "DataTypesAsLattices",
        section_order=DTAL_SECTION_ORDER,
        section_labels=DTAL_SECTION_LABELS,
        section_folders=DTAL_SECTION_FOLDERS,
        modules=modules,
        old=old,
        default_class_defs=[
            "  classDef c1 fill:#dcfce7,stroke:#15803d,color:#14532d",
            "  classDef c2 fill:#cffafe,stroke:#0e7490,color:#164e63",
            "  classDef c3 fill:#ffedd5,stroke:#c2410c,color:#7c2d12",
            "  classDef c4 fill:#ecfccb,stroke:#4d7c0f,color:#365314",
            "  classDef c5 fill:#f3e8ff,stroke:#7e22ce,color:#581c87",
            "  classDef c6 fill:#fde68a,stroke:#a16207,color:#713f12",
            "  classDef c7 fill:#e2e8f0,stroke:#334155,color:#0f172a",
        ],
    )


# 1980 Neighbourhood systems — one folder per section (see 1980_Neighborhood.md).
NS_SECTION_ORDER: list[str] = [
    "DOM",
    "MAP",
    "CON",
    "FIX",
    "LAM",
    "EQ",
    "COMP",
    "RET",
]
NS_SECTION_LABELS: dict[str, str] = {
    "DOM": "Domains given<br>by neighbourhoods",
    "MAP": "Mappings<br>between domains",
    "CON": "Domain<br>constructs",
    "FIX": "Fixed points<br>and recursion",
    "LAM": "Typed λ-calculus",
    "EQ": "Domain<br>equations",
    "COMP": "Computability in effectively given domains",
    "RET": "Retracts of the universal domain",
}
NS_SECTION_FOLDERS: dict[str, tuple[str, ...]] = {
    "DOM": ("DomainsGivenByNeighbourhoods",),
    "MAP": ("MappingsBetweenDomains",),
    "CON": ("DomainConstructs",),
    "FIX": ("FixedPointsAndRecursion",),
    "LAM": ("TypedLambdaCalculus",),
    "EQ": ("DomainEquations",),
    "COMP": ("ComputabilityInEffectivelyGivenDomains",),
    "RET": ("RetractsOfTheUniversalDomain",),
}


def gen_ns_sections(mermaid: Path, modules: dict[str, Path], old: str) -> str:
    """Cross-section Lean deps for 1980_Neighborhood.mermaid (folder ownership)."""
    return _gen_paper_section_deps(
        index_md_name="1980_Neighborhood.md",
        chapter_dir=DT / "NeighbourhoodSystems",
        section_order=NS_SECTION_ORDER,
        section_labels=NS_SECTION_LABELS,
        section_folders=NS_SECTION_FOLDERS,
        modules=modules,
        old=old,
        default_class_defs=[
            "  classDef c1 fill:#dbeafe,stroke:#1d4ed8,color:#1e3a8a",
            "  classDef c2 fill:#dcfce7,stroke:#15803d,color:#14532d",
            "  classDef c3 fill:#fef3c7,stroke:#b45309,color:#78350f",
            "  classDef c4 fill:#fce7f3,stroke:#be185d,color:#831843",
            "  classDef c5 fill:#fee2e2,stroke:#b91c1c,color:#7f1d1d",
            "  classDef c6 fill:#e0e7ff,stroke:#4338ca,color:#312e81",
            "  classDef c7 fill:#cffafe,stroke:#0e7490,color:#164e63",
            "  classDef c8 fill:#fae8ff,stroke:#a21caf,color:#701a75",
        ],
    )


# Lecture I hub: outline notes + companions for defs that lack @import Lean yet.
NS_DOM_COMPANIONS: dict[str, tuple[str, ...]] = {
    "Definition 1.7 — principal filter": ("principal",),
    "Definition 1.8 — approximation and totality": ("bot",),
    "Definition 1.9 — isomorphic domains": ("DomainIso",),
}
NS_DOM_SHORT: dict[str, tuple[str, str]] = {
    "Definition 1.1 — neighbourhood system": (
        "D11",
        "Definition 1.1<br>neighbourhood system",
    ),
    "Factoid 1.1 — empty intersection is delta; recursive finite intersection": (
        "F11",
        "Factoid 1.1",
    ),
    "Example 1.2 — two-token domain": ("E12", "Example 1.2<br>two-token domain"),
    "Example 1.3 — three-step chain": ("E13", "Example 1.3<br>three-step chain"),
    "Example 1.4 — finite binary tree": ("E14", "Example 1.4<br>finite binary tree"),
    "Factoid 1.4a — nested or disjoint": ("F14a", "Factoid 1.4a<br>nested or disjoint"),
    "Example 1.5 — all nonempty subsets": ("E15", "Example 1.5<br>all nonempty subsets"),
    "Factoid 1.5 — consistent iff nonempty; equivalent sequences same limit": (
        "F15",
        "Factoid 1.5",
    ),
    "Definition 1.6 — ideal elements": ("D16", "Definition 1.6<br>ideal elements"),
    "Definition 1.7 — principal filter": ("D17", "Definition 1.7<br>principal filter"),
    "Factoid 1.7 — principals are one-one; inclusion-reversing principals; union of principal filters": (
        "F17",
        "Factoid 1.7",
    ),
    "Definition 1.8 — approximation and totality": (
        "D18",
        "Definition 1.8<br>approximation and totality",
    ),
    "Factoid 1.8 — bottom element; bottom is least; finite filters are principal; prefix order; union of finite approximations": (
        "F18",
        "Factoid 1.8",
    ),
    "Examples 1.2–1.5 (Revisited) — finite examples revisited": (
        "ER",
        "Examples 1.2–1.5<br>revisited",
    ),
    "Definition 1.9 — isomorphic domains": (
        "D19",
        "Definition 1.9<br>isomorphic domains",
    ),
    "Theorem 1.10 — basic open neighbourhoods": (
        "T10",
        "Theorem 1.10<br>basic open neighbourhoods",
    ),
    "Theorem 1.11 — intersections and directed unions": (
        "T11",
        "Theorem 1.11<br>intersections and directed unions",
    ),
    "Lecture I exercises": ("EX", "Lecture I exercises"),
}


def _ns_dom_kind_class(nid: str) -> str:
    if nid.startswith("D"):
        return "cdef"
    if nid.startswith("F"):
        return "cfac"
    if nid.startswith("E") and nid != "EX":
        return "cexs"
    if nid == "ER":
        return "cexs"
    if nid.startswith("T"):
        return "cthm"
    if nid == "EX":
        return "cex"
    return "cdef"


def gen_ns_domains_lecture(mermaid: Path, modules: dict[str, Path], old: str) -> str:
    """Item-level Lean deps for 1980_Domains_given_by_neighbourhoods.mermaid."""
    header = [
        "%% Each box is one outline note from 1980_Domains_given_by_neighbourhoods.md.",
        "%% Lean modules = that note's @import .lean files (Lecture I exercises = all exercise modules;",
        "%%   Def 1.7/1.8/1.9 also own principal/bot/DomainIso).",
        "%% Arrowhead on the importer; label = direct-import count.",
        "%% Only paper-forward edges. Paths implied by longer routes omitted.",
    ]
    _, old_labels, style = parse_preserve_tail(old)
    index_md = find_index_md(mermaid)
    if index_md is None:
        raise ValueError(f"no index md for {mermaid}")
    folder = index_md.parent

    boxes: list[tuple[str, str, set[str]]] = []
    for line in index_md.read_text(encoding="utf-8", errors="ignore").splitlines():
        m = OUTLINE_LINK.match(line)
        if not m:
            continue
        title = m.group("title")
        child = resolve_md(index_md, m.group("href"))
        if child is None:
            continue
        if re.search(r"(?i)^introduction$", title.strip()):
            continue
        if title not in NS_DOM_SHORT:
            continue
        nid, default_lab = NS_DOM_SHORT[title]
        if title.lower().startswith("lecture") and "exercise" in title.lower():
            mods: set[str] = set()
            for ln in child.read_text(encoding="utf-8", errors="ignore").splitlines():
                mm = OUTLINE_LINK.match(ln)
                if not mm:
                    continue
                sub = resolve_md(child, mm.group("href"))
                if sub is not None:
                    mods |= lean_modules_from_note(sub)
        else:
            mods = set(lean_modules_from_note(child))
            for stem in NS_DOM_COMPANIONS.get(title, ()):
                p = folder / f"{stem}.lean"
                if p.is_file():
                    mods.add(module_of(p))
        if not mods:
            continue
        boxes.append((nid, old_labels.get(nid, default_lab), mods))

    mod_owner: dict[str, str] = {}
    for nid, _lab, mods in boxes:
        for mod in mods:
            mod_owner.setdefault(mod, nid)

    order = [nid for nid, _, _ in boxes]
    idx = {nid: i for i, nid in enumerate(order)}
    raw: dict[tuple[str, str], int] = defaultdict(int)
    for nid, _lab, mods in boxes:
        for mod in mods:
            for imp in direct_imports_mod(mod, modules):
                src = mod_owner.get(imp)
                if src is None or src == nid:
                    continue
                if idx[src] >= idx[nid]:
                    continue
                raw[(src, nid)] += 1

    kept = transitive_reduce(set(raw))
    edges = {(a, b): raw[(a, b)] for a, b in kept}
    node_labels = {nid: lab for nid, lab, _ in boxes}

    class_defs = [ln for ln in style if ln.strip().startswith("classDef ")]
    if not class_defs:
        class_defs = [
            "  classDef cdef fill:#dbeafe,stroke:#1d4ed8,color:#1e3a8a",
            "  classDef cfac fill:#dcfce7,stroke:#15803d,color:#14532d",
            "  classDef cexs fill:#fef3c7,stroke:#b45309,color:#78350f",
            "  classDef cex fill:#e0e7ff,stroke:#4338ca,color:#312e81",
            "  classDef cthm fill:#fee2e2,stroke:#b91c1c,color:#7f1d1d",
        ]
    class_assigns = [f"  class {nid} {_ns_dom_kind_class(nid)}" for nid in order]
    init = [ln for ln in style if INIT_LINE.match(ln.strip())]

    return emit_flowchart(
        header,
        node_labels,
        edges,
        init + class_defs + class_assigns,
        labeled=True,
        flowchart="flowchart TB",
        node_order=order,
    )


def cl1972_outline_box_modules(child: Path, title: str) -> set[str]:
    if re.match(r"(?i)introduction\s*$", title.strip()):
        return set()
    text = child.read_text(encoding="utf-8", errors="ignore")
    if any(OUTLINE_LINK.match(ln) for ln in text.splitlines()):
        return modules_from_section_outline(child)
    return lean_modules_from_note(child)


CONTINUOUS_LATTICES_SUBGRAPH_GROUPS: list[tuple[str, list[str]]] = [
    (
        "Definition 2.3 and Proposition 2.4",
        [
            "Definition 2.3: Continuous lattice",
            "Proposition 2.4",
        ],
    ),
    (
        "Idempotent fixed points",
        [
            "Idempotent fixed points",
            "Supremum on fixed points",
            "Complete lattice on fixed points",
        ],
    ),
    (
        "Theorem 2.12 and specialization",
        [
            "Injective space homeomorphic to a Scott continuous lattice",
            "Theorem 2.12",
            "Order isomorphism is a Scott homeomorphism",
            "Specialization equals the given complete-lattice order on injective T₀ spaces",
        ],
    ),
]

CONTINUOUS_LATTICES_RANK_SAME: list[list[str]] = [
    [
        "Definition 2.3: Continuous lattice",
        "Idempotent fixed points",
    ],
]

# Prose-only outline notes have no Lean @imports; narrative edges follow hub reading order.
COMPUTABILITY_OUTLINE_NARRATIVE: list[tuple[str, str]] = [
    ("Minimal and maximal extension", "Meaning"),
    ("Meaning", "The language LAMBDA"),
    ("The definability theorem", "A law of Y"),
]

# Reading-order edges for prose/tool notes that Lean edges may skip.
ENUMERATION_OUTLINE_NARRATIVE: list[tuple[str, str]] = [
    ("Introduction", "Term avoidance (α)"),
    ("Term avoidance (α)", "G-combinator tools"),
    ("G-combinator tools", "Theorem 3.1"),
    ("Theorem 3.1", "Application"),
    ("Application", "Unpairing"),
    ("Unpairing", "Numerals"),
    ("Numerals", "Val rank"),
    ("Val rank", "Theorem 3.2"),
    ("Theorem 3.2", "Recursion codes"),
    ("Recursion codes", "Theorem 3.3"),
]

DIRECTED_FIXPOINTS_OUTLINE_NARRATIVE: list[tuple[str, str]] = [
    ("Directed-sup way-below", "Directed compact fixed points"),
]

DEFINITION_RETRACT_OUTLINE_NARRATIVE: list[tuple[str, str]] = [
    ("Introduction", "Doubly strict conditional"),
    ("Doubly strict conditional", "Functional composition"),
]

RETRACTS_OUTLINE_NARRATIVE: list[tuple[str, str]] = [
    ("Introduction", "Graph lemmas"),
    ("Graph lemmas", "Predecessor set"),
    ("Predecessor set", "Fixpoints"),
    ("Fixpoints", "Directed fixpoints"),
    ("Directed fixpoints", "Definition (retract)"),
    ("Definition (retract)", "Theorem 4.1"),
    ("Theorem 4.1", "Definition (membership)"),
    ("Definition (membership)", "Definition (ordering)"),
    ("Definition (ordering)", "Open retract"),
    ("Open retract", "Theorem 4.2"),
    ("Theorem 4.2", "Theorem 4.3"),
    ("Theorem 4.3", "Theorem 4.4"),
    ("Theorem 4.4", "Theorem 4.5"),
    ("Theorem 4.5", "Theorem 4.6"),
]

# Tool-note reading order only. Theorem boxes use Lean import edges
# (5.1–5.4 are independent; 5.6 imports 5.3 and 5.5).
CLOSURES_OUTLINE_NARRATIVE: list[tuple[str, str]] = [
    ("Introduction", "Isolated"),
    ("Isolated", "Bottom"),
    ("Bottom", "Square pair"),
    ("Square pair", "Predecessor identities"),
    ("Predecessor identities", "Directed finite cover"),
    ("Directed finite cover", "Is compact"),
    ("Is compact", "Continuous basis"),
    ("Continuous basis", "Countably algebraic"),
    ("Countably algebraic", "Representation"),
    ("Representation", "Closure operation"),
]

# Tool-note reading order. Theorem boxes use Lean import edges.
CLASSIFICATION_OUTLINE_NARRATIVE: list[tuple[str, str]] = [
    ("Introduction", "Scott classes"),
    ("Scott classes", "Characteristic maps"),
    ("Characteristic maps", "Odd-even packing"),
    ("Odd-even packing", "Pair indexing"),
    ("Pair indexing", "F∩Gδ packing"),
    ("F∩Gδ packing", "Three-valued"),
    ("Three-valued", "Boolean membership"),
]

FUNCTIONALITY_OUTLINE_NARRATIVE: list[tuple[str, str]] = [
    ("Introduction", "Restricted equivalence relations"),
    ("Restricted equivalence relations", "Theorem 7.1"),
    ("Theorem 7.1", "Theorem 7.2"),
    ("Theorem 7.2", "Theorem 7.3"),
    ("Theorem 7.3", "Theorem 7.4"),
]

DEFINABILITY_THEOREM_OUTLINE_NARRATIVE: list[tuple[str, str]] = [
    ("Elementary definitions", "Primitive recursion"),
    ("Primitive recursion", "Definition (computable)"),
    ("Definition (computable)", "Definability"),
]

def restore_orphan_outline_edges(
    full: dict[tuple[str, str], int],
    reduced: dict[tuple[str, str], int],
    node_ids: set[str],
) -> dict[tuple[str, str], int]:
    """Put back one strongest incident edge for any node left isolated by reduction."""
    out = dict(reduced)

    def degree(nid: str) -> int:
        return sum(1 for a, b in out if a == nid or b == nid)

    for nid in node_ids:
        if degree(nid) > 0:
            continue
        candidates = [
            ((a, b), c) for (a, b), c in full.items() if (a == nid or b == nid) and c > 0
        ]
        if not candidates:
            continue
        (a, b), c = max(candidates, key=lambda x: x[1])
        out[(a, b)] = c
    return out


def cl1972_chapter_section_modules(modules: dict[str, Path]) -> dict[str, set[str]]:
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
            out[sec_id] = modules_from_section_outline(md, modules)
    return out


def cl1972_external_sections(
    for_section: str, modules: dict[str, Path]
) -> dict[str, tuple[str, set[str]]]:
    """Other chapter sections as importer sources (title, module set)."""
    all_mods = cl1972_chapter_section_modules(modules)
    return {
        sec_id: (CL1972_SECTION_LABELS[sec_id], all_mods[sec_id])
        for sec_id in all_mods
        if sec_id != for_section
    }


def index_md_is_outline_barrel(mermaid: Path) -> bool:
    """Note page imports this mermaid and lists child outline links (not a § hub)."""
    if mermaid.name in CL1972_SECTION_MERMAIDS:
        return False
    index_md = find_index_md(mermaid)
    if index_md is None:
        return False
    text = index_md.read_text(encoding="utf-8", errors="ignore")
    if f'@import "{mermaid.name}"' not in text:
        return False
    return any(OUTLINE_LINK.match(ln) for ln in text.splitlines())


def classify(mermaid: Path, text: str) -> str:
    if mermaid.name in CL1972_SECTION_MERMAIDS:
        return "cl1972_section"
    if mermaid.name == "1976_DataTypes.mermaid":
        return "dtal_sections"
    if mermaid.name == "1980_Neighborhood.mermaid":
        return "ns_sections"
    if mermaid.name == "1980_Domains_given_by_neighbourhoods.mermaid":
        return "ns_domains_lecture"
    if index_md_is_outline_barrel(mermaid):
        return "note_outline"
    if mermaid.name == "1972_ContinuousLattices.mermaid":
        return "cl1972_chapter"
    if mermaid.name == "DomainTheory.mermaid":
        return "top_chapters"
    if mermaid.name == "Specialization.mermaid" and mermaid.parent.name == "Specialization":
        return "note_outline"
    if mermaid.name == "WayBelow.mermaid" and mermaid.parent.name == "WayBelow":
        return "note_outline"
    if mermaid.name == "DirectedFixpoints.mermaid" and mermaid.parent.name == "Retracts":
        return "note_outline"
    if mermaid.name == "DefinitionRetract.mermaid" and mermaid.parent.name == "Retracts":
        return "note_outline"
    if mermaid.name == "ContinuousLattices.mermaid" and mermaid.parent.name == "ContinuousLattices":
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
    if "Each box is one section from 1976_DataTypes" in text:
        return "dtal_sections"
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
    if kind == "dtal_sections":
        return gen_dtal_sections(mermaid, modules, old)
    if kind == "cl1972_section":
        section_flowchart = (
            "flowchart TD"
            if mermaid.name == "1972_4_Inverse_limits.mermaid"
            else "flowchart LR"
        )
        return gen_note_outline(
            mermaid,
            modules,
            old,
            reduce=True,
            box_modules_fn=cl1972_outline_box_modules,
            flowchart=section_flowchart,
        )
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
            reduce=True,
            box_modules_fn=cl1972_outline_box_modules,
            extra_title_ids=cl_ids,
            header_lines=[
                "%% Each box is one section from 1972_ContinuousLattices.md (Introduction omitted).",
                "%% Lean modules = transitive closure of outline notes in that section.",
                "%% Arrowhead on the importer. An arrow implied by a longer path is omitted.",
            ],
        )
    if kind == "ns_sections":
        return gen_ns_sections(mermaid, modules, old)
    if kind == "ns_domains_lecture":
        return gen_ns_domains_lecture(mermaid, modules, old)
    if kind == "ns_items":
        return gen_neighborhood_items(mermaid, modules, old)
    if kind == "note_outline":
        skip = "Imports of a folder barrel are not counted" in old
        reduce = True
        extra_ids: dict[str, str] | None = None
        header_lines: list[str] | None = None
        if mermaid.name == "Specialization.mermaid":
            header_lines = [
                "%% Notes of the specialization order, in outline order.",
                *outline_mermaid_header("1972_Specialization_order.md"),
            ]
            extra_ids = {
                "Monotone nets": "MN",
                "Scott convergence": "SCT",
                "Specialization preorder": "SLe",
                "Scott topology on a complete lattice": "STS",
                "Scott-open sets": "SO",
                "Proposition 2.1": "P21",
            }
        if mermaid.name == "WayBelow.mermaid":
            header_lines = [
                "%% Notes of the way-below relation, in outline order.",
                *outline_mermaid_header("1972_WayBelow_order.md"),
            ]
            extra_ids = {
                "Way-below relation": "WB",
                "Proposition 2.2": "P22",
            }
        include_empty_boxes = False
        force_edges: list[tuple[str, str]] | None = None
        edge_filter_fn: Callable[[str, str], bool] | None = None
        outline_transitive_modules = True
        cl_subgraphs = None
        cl_rank_same = None
        cl_subgraph_directions: dict[str, str] | None = None
        collapse_hub: str | tuple[str, str] | None = None
        exclude_titles: frozenset[str] | None = None
        if mermaid.name == "FixedPoint.mermaid":
            extra_ids = {
                **(extra_ids or {}),
                "Iteration from $\\bot$ and **fix**": "ITER",
            }

            def _fixed_point_edge_filter(src: str, _dst: str) -> bool:
                # Theorem 1.3 (substitution) does not import iteration; drop spurious shared-module edges.
                return src != "Theorem 1.3"

            edge_filter_fn = _fixed_point_edge_filter
        if mermaid.name == "1976_Computability_and_definability.mermaid":
            include_empty_boxes = True
            force_edges = COMPUTABILITY_OUTLINE_NARRATIVE
            header_lines = [
                *outline_mermaid_header("1976_Computability_and_definability.md"),
                "%% Prose-only hub links (no Lean) are omitted from the diagram.",
            ]
            extra_ids = {
                **(extra_ids or {}),
                "Minimal and maximal extension": "EXT",
                "Meaning": "MEAN",
                "LAMBDA": "LAM",
                "The language LAMBDA": "LAM",
                "$\\lambda$-calculus as a formal language": "LAM",
                "Definition (computable)": "DCOMP",
                "Definability": "DEF",
                "Theorem 2.6": "T26",
                "Theorem 2.6 — the definability theorem": "T26",
                "The definability theorem": "DEFTHM",
                "A law of Y": "LAWY",
            }
        if mermaid.name == "Enumeration.mermaid":
            include_empty_boxes = True
            force_edges = ENUMERATION_OUTLINE_NARRATIVE
            header_lines = [
                *outline_mermaid_header("1976_Enumeration_and_degrees.md"),
                "%% Reading order for tool notes; Lean edges for theorem deps.",
            ]
            extra_ids = {
                **(extra_ids or {}),
                "Introduction": "INTRO",
                "Term avoidance (α)": "AVOID",
                "G-combinator tools": "GTOOLS",
                "Theorem 3.1": "T31",
                "Application": "APP",
                "Unpairing": "UNP",
                "Numerals": "NUM",
                "Val rank": "VRANK",
                "Theorem 3.2": "T32",
                "Recursion codes": "RCODE",
                "Plotkin helpers": "PHELP",
                "Theorem 3.3": "T33",
                "Theorem 3.4": "T34",
                "Theorem 3.5": "T35",
                "Theorem 3.6": "T36",
                "Theorem 3.7": "T37",
            }
        if mermaid.name == "Retracts.mermaid":
            include_empty_boxes = True
            force_edges = RETRACTS_OUTLINE_NARRATIVE
            header_lines = [
                *outline_mermaid_header("1976_Retracts_and_data_types.md"),
                "%% Reading order for definition notes; Lean edges for theorem deps.",
            ]
            extra_ids = {
                **(extra_ids or {}),
                "Introduction": "INTRO",
                "Graph lemmas": "GLEM",
                "Predecessor set": "PRED",
                "Fixpoints": "FIXP",
                "Directed fixpoints": "DFIX",
                "Definition (retract)": "DRET",
                "Theorem 4.1": "T41",
                "Definition (membership)": "DMEM",
                "Definition (ordering)": "DORD",
                "Open retract": "OPENR",
                "Theorem 4.2": "T42",
                "Theorem 4.3": "T43",
                "C combinators": "COMBC",
                "Pair mediation": "PMED",
                "Theorem 4.4": "T44",
                "Theorem 4.5": "T45",
                "Expression interpreter": "HINT",
                "Theorem 4.6": "T46",
            }
        if mermaid.name == "Closures.mermaid":
            include_empty_boxes = True
            force_edges = CLOSURES_OUTLINE_NARRATIVE
            header_lines = [
                *outline_mermaid_header("1976_Closure_operations_and_algebraic_lattices.md"),
                "%% Reading order for tool notes; Lean edges for theorem deps.",
            ]
            extra_ids = {
                **(extra_ids or {}),
                "Introduction": "INTRO",
                "Isolated": "ISOL",
                "Bottom": "BOT",
                "Square pair": "SQP",
                "Predecessor identities": "PRED",
                "Directed finite cover": "DFC",
                "Is compact": "ICMP",
                "Continuous basis": "CBAS",
                "Countably algebraic": "CALG",
                "Representation": "REP",
                "Closure operation": "DCLOS",
                "Definition (closure)": "DCLOS",
                "Theorem 5.1 — the algebraic lattice theorem": "T51",
                "Theorem 5.2 — the representation theorem": "T52",
                "Theorem 5.3 — the function space theorem": "T53",
                "Theorem 5.4 — the product and sum theorem": "T54",
                "Theorem 5.5 — the universe theorem": "T55",
                "Theorem 5.6 — the limit theorem": "T56",
            }
        if mermaid.name == "Classification.mermaid":
            include_empty_boxes = True
            force_edges = CLASSIFICATION_OUTLINE_NARRATIVE
            header_lines = [
                *outline_mermaid_header("1976_Subsets_and_their_classification.md"),
                "%% Reading order for tool notes; Lean edges for theorem deps.",
            ]
            extra_ids = {
                **(extra_ids or {}),
                "Introduction": "INTRO",
                "Scott classes": "DCLASS",
                "Characteristic maps": "CHAR",
                "Odd-even packing": "OEP",
                "Pair indexing": "PAIR",
                "F∩Gδ packing": "FGDP",
                "Three-valued": "TVAL",
                "Boolean membership": "BMEM",
                "Theorem 6.1": "T61",
                "Theorem 6.1 — the G theorem": "T61",
                "Theorem 6.2": "T62",
                "Theorem 6.2 — the F theorem": "T62",
                "Theorem 6.3": "T63",
                "Theorem 6.3 — the Gδ theorem": "T63",
                "Theorem 6.4": "T64",
                "Theorem 6.4 — the F∩G theorem": "T64",
                "Theorem 6.5": "T65",
                "Theorem 6.5 — the F∩Gδ theorem": "T65",
                "Theorem 6.6": "T66",
                "Theorem 6.6 — the B theorem": "T66",
                "Theorem 6.7": "T67",
                "Theorem 6.7 — the Bδ theorem": "T67",
            }
        if mermaid.name == "Functionality.mermaid":
            include_empty_boxes = True
            force_edges = FUNCTIONALITY_OUTLINE_NARRATIVE
            header_lines = [
                *outline_mermaid_header("1976_Total_functions_and_functionality.md"),
                "%% Reading order for tool notes; Lean edges for theorem deps.",
            ]
            extra_ids = {
                **(extra_ids or {}),
                "Introduction": "INTRO",
                "Pair elements": "PAIR",
                "Restricted equivalence relations": "DEQUIV",
                "Theorem 7.1": "T71",
                "Theorem 7.2": "T72",
                "Theorem 7.3": "T73",
                "Theorem 7.4": "T74",
            }
        if mermaid.name == "DirectedFixpoints.mermaid":
            include_empty_boxes = True
            force_edges = DIRECTED_FIXPOINTS_OUTLINE_NARRATIVE
            header_lines = [
                "%% Notes under Directed fixpoints, in outline order.",
                *outline_mermaid_header("1976_Directed_fixpoints.md"),
            ]
            extra_ids = {
                **(extra_ids or {}),
                "Directed-sup way-below": "WBSUP",
                "Directed compact fixed points": "DCOMP",
            }
        if mermaid.name == "GcombTools.mermaid":
            include_empty_boxes = True
            # Direct imports only: shared Mathlib/Pomega deps would otherwise
            # invent ContinuityHelpers → PairSeq edges via first-owner attribution.
            outline_transitive_modules = False
            header_lines = [
                *outline_mermaid_header("1976_Gcomb_tools.md"),
                "%% Lean import edges among the four tool notes.",
            ]
            extra_ids = {
                **(extra_ids or {}),
                "Continuity helpers": "CONT",
                "Pair sequences": "PSEQ",
                "Sum mediation": "SMED",
                "Z combinator": "ZCOMB",
            }
        if mermaid.name == "DefinitionRetract.mermaid":
            include_empty_boxes = True
            force_edges = DEFINITION_RETRACT_OUTLINE_NARRATIVE
            header_lines = [
                "%% Notes under Definition (retract), in outline order.",
                *outline_mermaid_header("1976_Definition_retract.md"),
            ]
            extra_ids = {
                **(extra_ids or {}),
                "Introduction": "DRINTRO",
                "Doubly strict conditional": "DCOND",
                "Functional composition": "FCOMP",
            }
        if mermaid.name == "1976_The_definability_theorem.mermaid":
            include_empty_boxes = True
            force_edges = DEFINABILITY_THEOREM_OUTLINE_NARRATIVE
            extra_ids = {
                **(extra_ids or {}),
                "Definition (computable)": "DCOMP",
                "Definability": "DEF",
                "Theorem 2.6": "T26",
                "Theorem 2.6 — the definability theorem": "T26",
            }
            header_lines = [
                *outline_mermaid_header("1976_The_definability_theorem.md"),
                "%% Reading order for prose-only steps; Lean edges for the rest.",
            ]
        if mermaid.name == "ContinuousLattices.mermaid":
            cl_subgraphs = CONTINUOUS_LATTICES_SUBGRAPH_GROUPS
            cl_rank_same = CONTINUOUS_LATTICES_RANK_SAME
            header_lines = [
                "%% Notes of the continuous lattice section, in outline order.",
                *outline_mermaid_header("1972_Continuous_lattice_order.md"),
                "%% Subgraphs follow dependency shape; hub list order is unchanged.",
            ]
            extra_ids = {
                "Definition 2.3: Continuous lattice": "D23",
                "Definition 2.3": "D23",
                "Proposition 2.4": "P24",
                "Limits and convergence": "LAC",
                "Injective space homeomorphic to a Scott continuous lattice": "IHCL",
                "Theorem 2.12": "T212",
                "Specialization equals the given complete-lattice order on injective T₀ spaces": "SELI",
                "Order isomorphism is a Scott homeomorphism": "OISH",
                "After Theorem 2.12": "A212",
                "Idempotent fixed points": "IFP",
                "Supremum on fixed points": "IFPS",
                "Complete lattice on fixed points": "IFPCL",
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
            extra_title_ids=extra_ids,
            header_lines=header_lines,
            include_empty_outline_boxes=include_empty_boxes,
            subgraph_groups=cl_subgraphs,
            rank_same_titles=cl_rank_same,
            subgraph_directions=cl_subgraph_directions,
            force_outline_edges=force_edges,
            edge_filter=edge_filter_fn,
            collapse_hub_into_subgraph=collapse_hub,
            exclude_outline_titles=exclude_titles,
            transitive_modules=outline_transitive_modules,
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
