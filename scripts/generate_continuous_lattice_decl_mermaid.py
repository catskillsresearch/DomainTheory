#!/usr/bin/env python3
"""Build ContinuousLattice.mermaid: consumes → produces over Lean declarations."""

from __future__ import annotations

import re
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CL = ROOT / "DomainTheory" / "ContinuousLattice"
OUT = CL / "ContinuousLattice.mermaid"

# Module wrappers only; keep `ContinuousLattice`, `ScottMap`, etc. for grouping.
SKIP_NS = frozenset({"DomainTheory"})

DECL_START = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+"
    r"([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)"
)
NS_START = re.compile(r"^namespace\s+([A-Za-z_][\w']*)\s*$")
NS_END = re.compile(r"^end\s+([A-Za-z_][\w']*)\s*$")

SKIP_NAMES = {
    "by", "of", "if", "then", "else", "have", "show", "let", "fun", "where",
    "with", "for", "in", "do", "pure", "return", "open", "set", "Set", "Type",
    "Prop", "Sort", "True", "False", "And", "Or", "Not", "Eq", "Iff", "Exists",
    "Nat", "Int", "Bool", "List", "Option", "Sum", "Prod", "Unit", "Empty",
    "id", "sorry", "rfl", "trivial", "simp", "rw", "exact", "apply", "intro",
    "constructor", "cases", "induction", "refine", "use", "obtain", "rcases",
    "ext", "congr", "calc", "suffices", "change", "convert", "specialize",
    "module", "namespace", "section", "end", "variable", "universe",
    "import", "public", "private", "protected", "scoped", "local",
    "noncomputable", "partial", "unsafe", "attribute",
    "CompleteLattice", "TopologicalSpace", "Monotone", "Continuous", "IsOpen",
    "Set", "Finset", "DirectedOn", "Directed", "sSup", "sInf", "iSup", "iInf",
}


def strip_comments(text: str) -> str:
    text = re.sub(r"/--.*?-/", " ", text, flags=re.S)
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    text = re.sub(r"--.*?$", " ", text, flags=re.M)
    return text


def name_referenced(text: str, name: str) -> bool:
    if re.search(rf"(?<![A-Za-z0-9_'.]){re.escape(name)}(?![A-Za-z0-9_'])", text):
        return True
    if re.search(rf"\.{re.escape(name)}\b", text):
        return True
    if "." in name:
        short = name.rsplit(".", 1)[-1]
        if short != name and re.search(rf"\.{re.escape(short)}\b", text):
            return True
    return False


def folder_of(path: Path) -> str:
    rel = path.relative_to(CL)
    return rel.parts[0] if len(rel.parts) > 1 else "Root"


def parse_decls(path: Path) -> list[dict]:
    lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
    ns_stack: list[str] = []
    starts: list[tuple[int, str, str, str | None]] = []

    for i, line in enumerate(lines):
        st = line.strip()
        m_ns = NS_START.match(st)
        if m_ns:
            ns_stack.append(m_ns.group(1))
            continue
        m_end = NS_END.match(st)
        if m_end:
            name = m_end.group(1)
            if ns_stack and ns_stack[-1] == name:
                ns_stack.pop()
            elif name in ns_stack:
                while ns_stack and ns_stack[-1] != name:
                    ns_stack.pop()
                if ns_stack:
                    ns_stack.pop()
            continue
        m = DECL_START.match(st)
        if not m:
            continue
        inner_ns = None
        for n in reversed(ns_stack):
            if n not in SKIP_NS:
                inner_ns = n
                break
        starts.append((i, m.group(1), m.group(2), inner_ns))

    out: list[dict] = []
    for j, (start, kind, name, inner_ns) in enumerate(starts):
        end = starts[j + 1][0] if j + 1 < len(starts) else len(lines)
        rel = path.relative_to(CL)
        uid = f"{rel}::{name}"
        out.append(
            {
                "uid": uid,
                "kind": kind,
                "name": name,
                "path": path,
                "folder": folder_of(path),
                "start": start,
                "end": end,
                "inner_ns": inner_ns,
            }
        )
    return out


def build_groups(decls: list[dict]) -> tuple[dict[str, dict], dict[str, str]]:
    """Return group metadata and decl uid -> display node key."""
    by_file: dict[Path, list[dict]] = defaultdict(list)
    for d in decls:
        by_file[d["path"]].append(d)

    global_anchors: dict[str, list[dict]] = defaultdict(list)
    for d in decls:
        if "." not in d["name"]:
            global_anchors[d["name"]].append(d)

    groups: dict[str, dict] = {}
    uid_to_node: dict[str, str] = {}

    def absorb(gkey: str, g: dict, d: dict, member_label: str) -> None:
        if d["uid"] == g["anchor_uid"]:
            return
        if d["uid"] in g["member_uids"]:
            return
        g["member_uids"].append(d["uid"])
        g["members"].append(member_label)

    for path, file_decls in by_file.items():
        rel = path.relative_to(CL)
        anchors: dict[str, dict] = {}
        for d in file_decls:
            if "." not in d["name"]:
                anchors[d["name"]] = d

        file_groups: dict[str, list[str]] = defaultdict(list)

        for d in file_decls:
            for xxx, anchor in anchors.items():
                if d["uid"] == anchor["uid"]:
                    continue
                if d["name"].startswith(xxx + "."):
                    file_groups[xxx].append(d["name"][len(xxx) + 1 :])
                    break
                if d["inner_ns"] == xxx:
                    file_groups[xxx].append(d["name"].split(".")[-1])
                    break

        for xxx, members in file_groups.items():
            if not members or xxx not in anchors:
                continue
            gkey = f"{rel}::@{xxx}"
            groups[gkey] = {
                "key": gkey,
                "name": xxx,
                "folder": folder_of(path),
                "members": sorted(set(members)),
                "anchor_uid": anchors[xxx]["uid"],
                "member_uids": [
                    d["uid"]
                    for d in file_decls
                    if d["uid"] != anchors[xxx]["uid"]
                    and (
                        d["name"].startswith(xxx + ".")
                        or d["inner_ns"] == xxx
                    )
                ],
            }

    # Dotted companions in other files (unique anchor name library-wide).
    for d in decls:
        if "." not in d["name"]:
            continue
        xxx, suffix = d["name"].split(".", 1)
        anchors = global_anchors.get(xxx, [])
        if len(anchors) != 1:
            continue
        anchor = anchors[0]
        rel = anchor["path"].relative_to(CL)
        gkey = f"{rel}::@{xxx}"
        if gkey not in groups:
            groups[gkey] = {
                "key": gkey,
                "name": xxx,
                "folder": folder_of(anchor["path"]),
                "members": [],
                "anchor_uid": anchor["uid"],
                "member_uids": [],
            }
        absorb(gkey, groups[gkey], d, suffix)

    for g in groups.values():
        g["members"] = sorted(set(g["members"]))

    for d in decls:
        placed = False
        for g in groups.values():
            if d["uid"] == g["anchor_uid"] or d["uid"] in g["member_uids"]:
                uid_to_node[d["uid"]] = g["key"]
                placed = True
                break
        if not placed:
            uid_to_node[d["uid"]] = d["uid"]

    return groups, uid_to_node


def mermaid_escape(label: str) -> str:
    return label.replace('"', "'")


def mermaid_id(key: str, used: set[str]) -> str:
    base = re.sub(r"[^A-Za-z0-9_]", "_", key)
    if not base or base[0].isdigit():
        base = f"n_{base}"
    cand = base
    n = 0
    while cand in used:
        n += 1
        cand = f"{base}_{n}"
    used.add(cand)
    return cand


def node_label(name: str, members: list[str]) -> str:
    if not members:
        return mermaid_escape(name)
    lines = [mermaid_escape(name)] + [mermaid_escape(m) for m in members]
    return "<br/>".join(lines)


def split_signature_body(text: str, kind: str) -> tuple[str, str]:
    text = strip_comments(text)
    m = re.search(r":=", text)
    if m is None:
        return text, ""
    return text[: m.start()], text[m.start() :]


def collect_type_chunks(signature: str) -> list[str]:
    """Type expressions from binders, instance args, and structure/class fields."""
    chunks: list[str] = []
    sig = signature
    i = 0
    n = len(sig)
    while i < n:
        if sig[i] in "([":
            close = ")" if sig[i] == "(" else "]"
            open_c = sig[i]
            depth = 1
            j = i + 1
            while j < n and depth > 0:
                if sig[j] == open_c:
                    depth += 1
                elif sig[j] == close:
                    depth -= 1
                j += 1
            inner = sig[i + 1 : j - 1]
            if ":" in inner:
                _, typ = inner.split(":", 1)
                chunks.append(typ.strip())
            else:
                chunks.append(inner.strip())
            i = j
        else:
            i += 1
    for m in re.finditer(
        r"(?m)^\s*(?:[\[\]@][^\n]*\n\s*)*[A-Za-z_][\w']*\s*:\s*(.+?)\s*$",
        sig,
    ):
        chunks.append(m.group(1).strip())
    extends = re.search(r"\bextends\s+(.+?)(?:\s+where\b|\s*$)", sig, re.S)
    if extends:
        chunks.append(extends.group(1).strip())
    ret = re.search(r"\)\s*:\s*(.+)$", sig.strip(), re.S)
    if ret:
        chunks.append(ret.group(1).strip())
    elif re.match(
        r"^(?:theorem|lemma|def|abbrev|instance)\s+\S+\s*:\s*(.+)$",
        sig.strip(),
        re.S,
    ):
        m = re.match(
            r"^(?:theorem|lemma|def|abbrev|instance)\s+\S+\s*:\s*(.+)$",
            sig.strip(),
            re.S,
        )
        if m:
            chunks.append(m.group(1).strip())
    return [c for c in chunks if c]


def refs_in_corpus(text: str, decls: list[dict], self_uid: str) -> set[str]:
    found: set[str] = set()
    for other in decls:
        if other["uid"] == self_uid:
            continue
        oname = other["name"]
        if oname in SKIP_NAMES or oname.split(".")[-1] in SKIP_NAMES:
            continue
        if name_referenced(text, oname):
            found.add(other["uid"])
    return found


def transitive_reduce(edges: set[tuple[str, str]]) -> set[tuple[str, str]]:
    succ: dict[str, set[str]] = defaultdict(set)
    for a, b in edges:
        succ[a].add(b)

    def reachable_without_direct(u: str, target: str) -> bool:
        stack = [w for w in succ[u] if w != target]
        seen: set[str] = set()
        while stack:
            w = stack.pop()
            if w == target:
                return True
            if w in seen:
                continue
            seen.add(w)
            stack.extend(succ[w])
        return False

    return {(u, v) for u, v in edges if not reachable_without_direct(u, v)}


def main() -> None:
    decls: list[dict] = []
    for path in sorted(CL.rglob("*.lean")):
        decls.extend(parse_decls(path))

    groups, uid_to_node = build_groups(decls)

    type_edges: set[tuple[str, str]] = set()
    call_edges: set[tuple[str, str]] = set()

    for d in decls:
        lines = d["path"].read_text(encoding="utf-8", errors="ignore").splitlines()
        raw = "\n".join(lines[d["start"] : d["end"]])
        sig, body = split_signature_body(raw, d["kind"])
        caller = uid_to_node[d["uid"]]

        type_text = " ".join(collect_type_chunks(sig))
        for ref_uid in refs_in_corpus(type_text, decls, d["uid"]):
            type_node = uid_to_node[ref_uid]
            if type_node != caller:
                type_edges.add((type_node, caller))

        for ref_uid in refs_in_corpus(body, decls, d["uid"]):
            callee = uid_to_node[ref_uid]
            if callee != caller:
                # Callee → caller (YYY uses XXX as XXX --> YYY).
                call_edges.add((callee, caller))

    call_edges = transitive_reduce(call_edges)

    # Display nodes: groups + standalone decls.
    display_nodes: dict[str, dict] = {}
    for gkey, g in groups.items():
        display_nodes[gkey] = {
            "key": gkey,
            "name": g["name"],
            "folder": g["folder"],
            "members": g["members"],
        }
    for d in decls:
        if uid_to_node[d["uid"]] == d["uid"]:
            display_nodes[d["uid"]] = {
                "key": d["uid"],
                "name": d["name"],
                "folder": d["folder"],
                "members": [],
            }

    used_ids: set[str] = set()
    key_to_nid: dict[str, str] = {}
    for key, node in display_nodes.items():
        key_to_nid[key] = mermaid_id(key, used_ids)

    folders = sorted({n["folder"] for n in display_nodes.values()})

    header = [
        "%% ContinuousLattice (top level). Each box is one Lean name, or a parent",
        "%% with its namespace / dotted companions listed inside the label.",
        "%% Green dotted: type/name in a declaration's binders or fields → that declaration.",
        "%% Blue solid: callee → caller (head calls tail). Redundant call paths omitted.",
        "flowchart TB",
        "",
    ]

    lines_out = header[:]
    by_folder: dict[str, list[dict]] = defaultdict(list)
    for node in display_nodes.values():
        by_folder[node["folder"]].append(node)

    for folder in folders:
        sg = re.sub(r"[^A-Za-z0-9_]", "_", folder)
        lines_out.append(f'  subgraph {sg}["{mermaid_escape(folder)}"]')
        lines_out.append("    direction TB")
        for node in sorted(by_folder[folder], key=lambda x: x["name"].lower()):
            nid = key_to_nid[node["key"]]
            label = node_label(node["name"], node["members"])
            lines_out.append(f'    {nid}["{label}"]')
        lines_out.append("  end")
        lines_out.append("")

    edge_lines: list[str] = []
    link_styles: list[str] = []
    idx = 0

    for typ, user in sorted(
        type_edges, key=lambda p: (key_to_nid[p[0]], key_to_nid[p[1]])
    ):
        edge_lines.append(f"  {key_to_nid[typ]} -.-> {key_to_nid[user]}")
        link_styles.append(f"linkStyle {idx} stroke:#15803d,color:#15803d,stroke-width:2px")
        idx += 1

    for callee, caller in sorted(
        call_edges, key=lambda p: (key_to_nid[p[0]], key_to_nid[p[1]])
    ):
        edge_lines.append(f"  {key_to_nid[callee]} --> {key_to_nid[caller]}")
        link_styles.append(f"linkStyle {idx} stroke:#1d4ed8,color:#1d4ed8,stroke-width:2px")
        idx += 1

    lines_out.extend(edge_lines)
    lines_out.append("")
    lines_out.extend(link_styles)
    lines_out.append("")
    lines_out.append("  classDef node fill:#dbeafe,stroke:#1d4ed8,color:#1e3a8a")

    for key in display_nodes:
        lines_out.append(f"  class {key_to_nid[key]} node")

    OUT.write_text("\n".join(lines_out) + "\n", encoding="utf-8")
    print(
        f"Wrote {OUT.relative_to(ROOT)}: {len(display_nodes)} nodes, "
        f"{len(type_edges)} type edges, {len(call_edges)} call edges "
        f"({len(groups)} grouped, from {len(decls)} declarations)"
    )


if __name__ == "__main__":
    main()
