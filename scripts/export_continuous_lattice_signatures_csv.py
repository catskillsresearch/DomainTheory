#!/usr/bin/env python3
"""Export ContinuousLattice declaration signatures to CSV."""

from __future__ import annotations

import csv
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CL = ROOT / "DomainTheory" / "ContinuousLattice"
OUT = CL / "ContinuousLattice.csv"

DECL_START = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+"
    r"([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)"
)


def strip_comments(text: str) -> str:
    text = re.sub(r"/--.*?-/", " ", text, flags=re.S)
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    text = re.sub(r"--.*?$", " ", text, flags=re.M)
    return text


def signature_text(raw: str, kind: str) -> str:
    text = strip_comments(raw)
    if kind in ("structure", "class", "inductive", "instance"):
        m = re.search(r"\bwhere\b", text)
        if m:
            text = text[: m.start()]
    m = re.search(r":=", text)
    if m:
        text = text[: m.start()]
    text = re.sub(r"\s+", " ", text).strip()
    return text


def drop_decl_header(sig: str, kind: str, name: str) -> str:
    pat = rf"^{kind}\s+{re.escape(name)}\s*"
    m = re.match(pat, sig)
    if not m:
        return sig
    return sig[m.end() :].strip()


def split_top_level_type(typ: str) -> list[str]:
    """Split `(A) → B` or `A → B` into argument types + return (last component)."""
    typ = typ.strip()
    if not typ:
        return []
    parts: list[str] = []
    i = 0
    n = len(typ)
    while i < n:
        while i < n and typ[i].isspace():
            i += 1
        if i >= n:
            break
        start = i
        depth = 0
        while i < n:
            c = typ[i]
            if c in "([{":
                depth += 1
            elif c in ")]}":
                depth -= 1
            elif depth == 0 and typ[i : i + 2] in ("→", "->"):
                parts.append(typ[start:i].strip())
                i += 2
                while i < n and typ[i].isspace():
                    i += 1
                start = i
                continue
            i += 1
        parts.append(typ[start:].strip())
        break
    return [p for p in parts if p]


def parse_binder_chunk(inner: str) -> list[str]:
    inner = inner.strip()
    if not inner:
        return []
    if inner.startswith(":"):
        return [inner[1:].strip()]
    if ":" in inner:
        _, typ = inner.rsplit(":", 1)
        return [typ.strip()]
    return [inner]


def parse_binders(rest: str) -> tuple[list[str], str]:
    """Return (argument types, remainder after binders)."""
    args: list[str] = []
    i = 0
    n = len(rest)
    while i < n:
        while i < n and rest[i].isspace():
            i += 1
        if i >= n:
            break
        if rest[i] not in "({[":
            break
        open_c = rest[i]
        close = {"(": ")", "{": "}", "[": "]"}[open_c]
        depth = 1
        j = i + 1
        while j < n and depth > 0:
            if rest[j] == open_c:
                depth += 1
            elif rest[j] == close:
                depth -= 1
            j += 1
        inner = rest[i + 1 : j - 1]
        args.extend(parse_binder_chunk(inner))
        i = j
    return args, rest[i:].strip()


def parse_return(rest: str, kind: str, name: str) -> str:
    rest = rest.strip()
    if kind in ("structure", "class", "inductive"):
        if rest.startswith(": "):
            return rest[2:].strip() or name
        if rest.startswith(":"):
            return rest[1:].strip() or name
        if rest.startswith("extends "):
            return name
        return name
    if rest.startswith(": "):
        return rest[2:].strip()
    if rest.startswith(":"):
        return rest[1:].strip()
    m = re.search(r"\)\s*:\s*(.+)$", rest)
    if m:
        return m.group(1).strip()
    return ""


def extends_clause(sig_full: str) -> str:
    text = strip_comments(sig_full)
    m = re.search(r"\bextends\s+(.+?)(?:\s+where\b|\s*$)", text, re.S)
    if not m:
        return ""
    return re.sub(r"\s+", " ", m.group(1).strip())


def structure_field_types(raw: str) -> list[str]:
    text = strip_comments(raw)
    lines = text.splitlines()
    where_i = next((i for i, ln in enumerate(lines) if re.search(r"\bwhere\b", ln)), None)
    if where_i is None:
        return []
    field_start = re.compile(r"^(\s+)([A-Za-z_][\w']*)\s*:\s*(.*)$")
    types: list[str] = []
    current: str | None = None
    base_indent: str | None = None

    for ln in lines[where_i + 1 :]:
        if re.match(r"^\s*end\b", ln):
            break
        m = field_start.match(ln)
        if m:
            if current is not None:
                types.append(current)
            base_indent = m.group(1)
            rest = m.group(3).strip()
            if ":=" in rest:
                rest = rest.split(":=", 1)[0].strip()
            current = rest
            continue
        if current is None:
            continue
        if not ln.strip():
            continue
        if base_indent and len(ln) - len(ln.lstrip()) <= len(base_indent) and ":" in ln:
            types.append(current)
            current = None
            base_indent = None
            m2 = field_start.match(ln)
            if m2:
                base_indent = m2.group(1)
                rest = m2.group(3).strip()
                if ":=" in rest:
                    rest = rest.split(":=", 1)[0].strip()
                current = rest
            continue
        cont = ln.strip()
        if ":=" in cont:
            cont = cont.split(":=", 1)[0].strip()
        current = (current + " " + cont).strip()

    if current is not None:
        types.append(current)
    return [re.sub(r"\s+", " ", t).strip() for t in types if t.strip()]


def decl_end(lines: list[str], start: int, kind: str) -> int:
    if kind in ("structure", "class", "inductive"):
        header_indent = len(lines[start]) - len(lines[start].lstrip())
        where_i = None
        for i in range(start, len(lines)):
            if re.search(r"\bwhere\b", lines[i]):
                where_i = i
                break
        if where_i is None:
            return start + 1
        i = where_i + 1
        while i < len(lines):
            ln = lines[i]
            if not ln.strip():
                i += 1
                continue
            cur = len(ln) - len(ln.lstrip())
            if cur <= header_indent:
                break
            i += 1
        return i

    i = start
    while i < len(lines) and ":=" not in lines[i]:
        i += 1
    if i >= len(lines):
        return len(lines)
    line = lines[i]
    if re.search(r":=\s*by\b", line) or line.rstrip().endswith("by"):
        i += 1
        while i < len(lines):
            ln = lines[i]
            if not ln.strip():
                j = i + 1
                while j < len(lines) and not lines[j].strip():
                    j += 1
                if j < len(lines) and lines[j][:1].isspace():
                    i = j
                    continue
                return i
            if ln[0].isspace():
                i += 1
                continue
            if DECL_START.match(ln.strip()):
                return i
            if re.match(r"^(end|namespace|section)\b", ln.strip()):
                return i
            return i
    i += 1
    while i < len(lines):
        ln = lines[i]
        if not ln.strip():
            i += 1
            continue
        if ln[0].isspace():
            i += 1
            continue
        break
    return i


def parse_decls(path: Path) -> list[tuple[str, str, int, int]]:
    lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
    starts: list[tuple[int, str, str]] = []
    for i, line in enumerate(lines):
        st = line.strip()
        m = DECL_START.match(st)
        if m:
            starts.append((i, m.group(1), m.group(2)))
    out: list[tuple[str, str, int, int]] = []
    for j, (start, kind, name) in enumerate(starts):
        end = decl_end(lines, start, kind)
        if j + 1 < len(starts) and starts[j + 1][0] < end:
            end = starts[j + 1][0]
        out.append((kind, name, start, end))
    return out


def parse_signature(kind: str, name: str, raw: str) -> tuple[str, list[str]]:
    full = strip_comments(raw)
    sig = signature_text(raw, kind)
    sig_one = re.sub(r"\s+", " ", sig).strip()
    rest = drop_decl_header(sig_one, kind, name)

    arg_types, rest = parse_binders(rest)
    ret = parse_return(rest, kind, name)

    if kind in ("structure", "class", "inductive"):
        ext = extends_clause(full)
        if ext:
            arg_types.append(ext)
        arg_types.extend(structure_field_types(full))
        if not ret:
            ret = name

    if kind == "instance" and not ret:
        m = re.match(
            rf"^instance\s+(?:\([^)]*\)\s*)?(?::\s*)?(.+)$",
            sig_one,
        )
        if m:
            ret = m.group(1).strip()

    # Curried `(A) → B` in return: peel function types into extra args.
    if ret and kind in ("def", "abbrev", "theorem", "lemma"):
        arrow_parts = split_top_level_type(ret)
        if len(arrow_parts) > 1:
            arg_types.extend(arrow_parts[:-1])
            ret = arrow_parts[-1]

    return ret, arg_types


def main() -> None:
    rows: list[dict[str, str]] = []
    max_args = 0

    for path in sorted(CL.rglob("*.lean")):
        for kind, name, start, end in parse_decls(path):
            if kind == "lemma":
                kind = "theorem"
            raw = "\n".join(
                path.read_text(encoding="utf-8", errors="ignore").splitlines()[start:end]
            )
            ret, args = parse_signature(kind, name, raw)
            ret = re.sub(r"\s+", " ", ret).strip()
            args = [re.sub(r"\s+", " ", a).strip() for a in args]
            max_args = max(max_args, len(args))
            rows.append(
                {
                    "name": name,
                    "kind": kind,
                    "filename": path.relative_to(CL).as_posix(),
                    "return_type": ret,
                    "args": args,
                }
            )

    rows.sort(key=lambda r: (r["name"].lower(), r["filename"], r["kind"]))

    fieldnames = ["name", "kind", "filename", "return_type"] + [
        f"arg{i}_type" for i in range(1, max_args + 1)
    ]

    with OUT.open("w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames, extrasaction="ignore")
        w.writeheader()
        for r in rows:
            out = {
                "name": r["name"],
                "kind": r["kind"],
                "filename": r["filename"],
                "return_type": r["return_type"],
            }
            for i, arg in enumerate(r["args"], start=1):
                out[f"arg{i}_type"] = arg
            w.writerow(out)

    print(
        f"Wrote {OUT.relative_to(ROOT)}: {len(rows)} rows, "
        f"{max_args} arg columns max"
    )


if __name__ == "__main__":
    main()
