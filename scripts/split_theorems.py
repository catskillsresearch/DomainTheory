#!/usr/bin/env python3
"""Split theorem/lemma declarations into sibling files under ModuleName/."""

from __future__ import annotations

import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1] / "DomainTheory"
REPO = ROOT.parent

COPYRIGHT = """/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/
"""

DECL_HEAD = re.compile(
    r"^(\s*)"
    r"((?:@[^\n]*\]\s*)|(?:private|protected|noncomputable)\s+)*"
    r"(theorem|lemma)\s+([^\s(:]+)"
)
TOP_DECL = re.compile(
    r"^(\s*)"
    r"((?:@[^\n]*\]\s*)|(?:private|protected|noncomputable)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|class|structure|inductive|mutual|end|namespace)\b"
)
SECTION_HEAD = re.compile(r"^(\s*)section(\s|$)")


def is_top_level_decl_line(line: str) -> bool:
    if TOP_DECL.match(line):
        return True
    if SECTION_HEAD.match(line):
        return True
    if re.match(r"^\s*variable\b", line):
        return True
    if re.match(r"^\s*(include|omit)\b", line):
        return True
    return bool(DECL_HEAD.match(line))
IMPORT = re.compile(r"^import\s+")
DOC_BLOCK = re.compile(r"/--(?:[^-]|(-(?!/)))*?-/", re.DOTALL)
CONTEXT_LINE = re.compile(
    r"^(\s*)("
    r"namespace|end|open|variable|universe|set_option|include|omit|attribute"
    r"|--)\b"
)


def safe_module_name(name: str) -> str:
    """Lean module path segment. Subscripts must not collide (`inj₀` vs `inj₁`)."""
    out: list[str] = []
    for ch in name:
        if ch.isascii() and (ch.isalnum() or ch == "_"):
            out.append(ch)
        else:
            out.append(f"u{ord(ch):x}")
    return "".join(out)


@dataclass
class Decl:
    kind: str
    name: str
    start: int  # includes leading doc / attributes
    thm_line: int
    end: int  # exclusive
    indent: int


def find_mutual_ranges(lines: list[str]) -> list[tuple[int, int]]:
    ranges: list[tuple[int, int]] = []
    i = 0
    while i < len(lines):
        if lines[i].strip().startswith("mutual"):
            start = i
            depth = 0
            j = i
            while j < len(lines):
                s = lines[j].strip()
                if s.startswith("mutual"):
                    depth += 1
                if s.startswith("end") and "mutual" not in s:
                    depth -= 1
                    if depth == 0:
                        ranges.append((start, j + 1))
                        i = j + 1
                        break
                j += 1
            else:
                break
        else:
            i += 1
    return ranges


def in_mutual(line: int, ranges: list[tuple[int, int]]) -> bool:
    return any(a <= line < b for a, b in ranges)


def comment_ranges(lines: list[str]) -> list[tuple[int, int]]:
    """Half-open line ranges inside `/- … -/` blocks (including `/-!`, `/--`)."""
    ranges: list[tuple[int, int]] = []
    i = 0
    while i < len(lines):
        s = lines[i].strip()
        if s.startswith("/-") and not s.startswith("--"):
            start = i
            if s.endswith("-/"):
                ranges.append((start, i + 1))
                i += 1
                continue
            i += 1
            while i < len(lines):
                if lines[i].strip().endswith("-/"):
                    ranges.append((start, i + 1))
                    i += 1
                    break
                i += 1
            continue
        i += 1
    return ranges


def in_comment(line: int, ranges: list[tuple[int, int]]) -> bool:
    return any(a <= line < b for a, b in ranges)


def is_infix_or_notation_line(line: str) -> bool:
    """A real notation command, not prose that happens to start with `prefix`."""
    t = line.strip()
    return bool(
        re.match(
            r"(@\[.*?\]\s*)?(local\s+|scoped\s+)?(infix[lr]?|prefix|postfix|notation)\b.*=>",
            t,
        )
    )


def decl_block_start(lines: list[str], thm_line: int) -> int:
    """Doc / attributes immediately above this theorem only (not a prior theorem's `@`)."""
    start = thm_line
    j = thm_line - 1
    while j >= 0:
        if not lines[j].strip():
            j -= 1
            continue
        if DECL_HEAD.match(lines[j]) or is_top_level_decl_line(lines[j]):
            break
        if is_infix_or_notation_line(lines[j]):
            break
        s = lines[j].strip()
        if s.endswith("-/") and not s.startswith("/-") and not s.startswith("/--"):
            k = j
            while k >= 0 and not lines[k].strip().startswith("/-"):
                k -= 1
            if k >= 0 and lines[k].strip().startswith("/--"):
                start = k
                j = k - 1
                continue
            break
        if s.startswith("/--") and not s.startswith("/-!"):
            start = j
            if not s.endswith("-/"):
                k = j - 1
                while k >= 0:
                    if lines[k].strip().startswith("/--"):
                        start = k
                    if lines[k].strip().endswith("-/"):
                        break
                    if DECL_HEAD.match(lines[k]) or is_top_level_decl_line(lines[k]):
                        break
                    k -= 1
            j -= 1
            continue
        if s.startswith("@["):
            start = j
            j -= 1
            continue
        if re.match(r"^\s*(omit|include)\b", lines[j]):
            start = j
            j -= 1
            continue
        break
    return start


def next_decl_block_start(lines: list[str], from_line: int) -> int | None:
    i = from_line
    while i < len(lines):
        s = lines[i].strip()
        if not s:
            i += 1
            continue
        if s.startswith("/--") and not s.startswith("/-!"):
            k = i + 1
            while k < len(lines):
                if DECL_HEAD.match(lines[k]):
                    return i
                if lines[k].strip() and not lines[k].strip().startswith("--"):
                    if not lines[k].strip().startswith("/-"):
                        break
                k += 1
        if DECL_HEAD.match(lines[i]):
            return i
        i += 1
    return None


def decl_end(lines: list[str], thm_line: int) -> int:
    m = DECL_HEAD.match(lines[thm_line])
    assert m
    base = len(m.group(1))
    i = thm_line + 1
    while i < len(lines):
        line = lines[i]
        if not line.strip():
            i += 1
            continue
        indent = len(line) - len(line.lstrip())
        s = line.strip()
        if indent <= base and is_top_level_decl_line(line):
            break
        if indent <= base and (s.startswith("/--") or s.startswith("/-!")):
            break
        if indent <= base and re.match(
            r"^(open|universe|set_option|include|omit|attribute)\b", s
        ):
            break
        if indent <= base and re.match(r"^variable\b", s) and ":=" not in s:
            break
        if indent <= base:
            nxt = next_decl_block_start(lines, i)
            if nxt is not None and nxt == i:
                break
        i += 1
    return i


PRIVATE_DECL = re.compile(r"^(\s*)private\s+(def|abbrev|theorem|lemma)\s+(\S+)")


def expose_private_decls(basic_body: list[str], decls: list[Decl], lines: list[str]) -> None:
    """Make `private` declarations public in Basic when extracted theorems need them."""
    priv: set[str] = set()
    for ln in basic_body:
        m = PRIVATE_DECL.match(ln)
        if m:
            priv.add(m.group(3))
    if not priv:
        return
    needed: set[str] = set()
    for d in decls:
        text = decl_reference_text(lines[d.start : d.end])
        for name in priv:
            if name_referenced_in_text(text, name):
                needed.add(name)
    if not needed:
        return
    for i, ln in enumerate(basic_body):
        m = PRIVATE_DECL.match(ln)
        if m and m.group(3) in needed:
            basic_body[i] = re.sub(
                rf"^(\s*)private\s+((?:def|abbrev|theorem|lemma)\s+{re.escape(m.group(3))}\b)",
                r"\1\2",
                ln,
                count=1,
            )


def remove_redundant_private_theorem_blocks(
    basic_body: list[str], header: list[str]
) -> list[str]:
    """Drop `private theorem`s in Basic when an imported module already exports the name."""
    if not any("Approximable" in ln for ln in header if IMPORT.match(ln)):
        return basic_body
    out: list[str] = []
    i = 0
    while i < len(basic_body):
        m = PRIVATE_DECL.match(basic_body[i])
        if m and m.group(2) in ("theorem", "lemma") and m.group(3) == "singleton_funion_eq":
            j = i + 1
            while j < len(basic_body):
                s = basic_body[j].strip()
                if not s:
                    j += 1
                    continue
                if PRIVATE_DECL.match(basic_body[j]) or DECL_HEAD.match(basic_body[j]):
                    break
                if re.match(r"^\s*(def|abbrev|instance|class|structure|namespace|section)\b", s):
                    break
                j += 1
            i = j
            continue
        out.append(basic_body[i])
        i += 1
    return out


def decl_is_private(lines: list[str], d: Decl) -> bool:
    head = lines[d.thm_line]
    return bool(re.search(r"^\s*private\s+", head)) or bool(
        re.search(r"^\s*protected\s+", head)
    )


def parse_decls(lines: list[str]) -> list[Decl]:
    mutual = find_mutual_ranges(lines)
    comments = comment_ranges(lines)
    decls: list[Decl] = []
    i = 0
    while i < len(lines):
        m = DECL_HEAD.match(lines[i])
        if (
            m
            and m.group(3) in ("theorem", "lemma")
            and not in_mutual(i, mutual)
            and not in_comment(i, comments)
        ):
            blk = decl_block_start(lines, i)
            end = decl_end(lines, i)
            name = re.sub(r"\.\{.*$", "", m.group(4))
            decls.append(
                Decl(m.group(3), name, blk, i, end, len(m.group(1)))
            )
        i += 1
    return decls


def split_header(lines: list[str]) -> tuple[list[str], int]:
    """Return (header lines including doc, index where body starts)."""
    i = 0
    header: list[str] = []
    if i < len(lines) and lines[i].startswith("/-"):
        while i < len(lines):
            header.append(lines[i])
            i += 1
            if lines[i - 1].strip().endswith("-/"):
                break
    while i < len(lines) and (IMPORT.match(lines[i]) or lines[i].strip() == ""):
        header.append(lines[i])
        i += 1
    while i < len(lines) and lines[i].strip().startswith("/-!"):
        while i < len(lines):
            header.append(lines[i])
            i += 1
            if lines[i - 1].strip().endswith("-/"):
                break
    return header, i


def strip_theorem_blocks(lines: list[str], decls: list[Decl]) -> list[str]:
    skip = set()
    for d in decls:
        skip.update(range(d.start, d.end))
        skip.update(scoped_next_indices(lines, d.start))
    return [ln for i, ln in enumerate(lines) if i not in skip]


def is_decl_start_line(line: str) -> bool:
    s = line.strip()
    if not s or s.startswith("/-!"):
        return False
    if s.startswith("/--"):
        return False
    if s.startswith("@["):
        return False
    return is_top_level_decl_line(line)


def follows_top_level_decl(lines: list[str], k: int) -> bool:
    while k < len(lines) and not lines[k].strip():
        k += 1
    if k >= len(lines):
        return False
    if lines[k].strip().startswith("end"):
        return False
    if re.match(r"^\s*(omit|include|variable)\b", lines[k].strip()):
        return False
    if is_decl_start_line(lines[k]):
        return True
    # Structure / inductive field docs and fields must keep their preceding doc.
    if re.match(r"^\s+/--", lines[k]):
        return True
    if re.match(r"^\s+[\w'.]+\s*:", lines[k]):
        return True
    return False


def strip_irreducible_attributes(lines: list[str]) -> list[str]:
    """Remove `attribute [irreducible]` from Basic; it is re-emitted on later theorem files."""
    return [ln for ln in lines if not re.match(r"^\s*attribute\s+\[irreducible\]", ln)]


def skip_trivia_forward(lines: list[str], j: int) -> int:
    """Skip blanks, line comments, and `/- … -/` blocks."""
    while j < len(lines):
        s = lines[j].strip()
        if not s or s.startswith("--"):
            j += 1
            continue
        if s.startswith("/-"):
            if s.endswith("-/"):
                j += 1
                continue
            j += 1
            while j < len(lines) and not lines[j].strip().endswith("-/"):
                j += 1
            j = min(j + 1, len(lines))
            continue
        break
    return j


def strip_orphan_omit_include(lines: list[str]) -> list[str]:
    """Drop `omit`/`include` in Basic with no following theorem in the same file."""
    out: list[str] = []
    i = 0
    while i < len(lines):
        s = lines[i].strip()
        if re.match(r"^(omit|include)\b", s) and re.search(r"\bin\s*$", s):
            j = skip_trivia_forward(lines, i + 1)
            while j < len(lines) and SCOPED_NEXT.match(lines[j]):
                j = skip_trivia_forward(lines, j + 1)
            if j >= len(lines) or not DECL_HEAD.match(lines[j]):
                i += 1
                continue
        out.append(lines[i])
        i += 1
    return out


def cleanup_basic_tail(lines: list[str]) -> list[str]:
    """Drop trailing fragments left when a theorem's doc/omit/end were not in its strip range."""
    out = list(lines)
    changed = True
    while changed:
        changed = False
        while out and not out[-1].strip():
            out.pop()
            changed = True
        if not out:
            break
        s = out[-1].strip()
        if re.match(r"^(omit|include)\b", s):
            out.pop()
            changed = True
            continue
        if re.match(r"^end\b", s):
            out.pop()
            changed = True
            continue
        # A trailing comment. Delete only an orphan `/--` doc (its theorem was
        # extracted). A `/-!` or `/-` block stays, including every declaration
        # before it. Do not walk backwards through those.
        if s == "-/" or s.endswith("-/"):
            k = len(out) - 1
            while k >= 0 and not out[k].strip().startswith("/-"):
                k -= 1
            if k >= 0 and out[k].strip().startswith("/--"):
                del out[k:]
                changed = True
                continue
            break
    suffix = namespace_close_suffix(out)
    if suffix:
        out.append(suffix)
    return out


def remove_orphan_doc_comments(lines: list[str]) -> list[str]:
    out: list[str] = []
    i = 0
    while i < len(lines):
        s = lines[i].strip()
        if s.startswith("/--") and not s.startswith("/-!"):
            if s.endswith("-/"):
                j = i + 1
            else:
                j = i + 1
                while j < len(lines) and not lines[j].strip().endswith("-/"):
                    j += 1
                j = min(j + 1, len(lines))
            if not follows_top_level_decl(lines, j):
                i = j
                continue
        out.append(lines[i])
        i += 1
    return out


def is_context_line(line: str) -> bool:
    s = line.strip()
    if not s:
        return True
    if s.startswith("/-!"):
        return False
    if s.startswith("/--"):
        return False
    if s.startswith("@["):
        return False
    # Notation stays in Basic. Copying it into every theorem file redeclares it.
    if is_infix_or_notation_line(line):
        return False
    if SECTION_HEAD.match(line):
        return True
    return bool(CONTEXT_LINE.match(line))


def next_theorem_line(lines: list[str], after: int) -> int | None:
    """First `theorem`/`lemma` line strictly after `after`."""
    i = skip_trivia_forward(lines, after + 1)
    while i < len(lines):
        s = lines[i].strip()
        if DECL_HEAD.match(lines[i]):
            return i
        if is_top_level_decl_line(lines[i]) and not re.match(r"^(omit|include)\b", s):
            return None
        i = skip_trivia_forward(lines, i + 1)
    return None


def omit_include_for_decl(lines: list[str], d: Decl) -> list[str]:
    """`omit` / `include` lines that apply only to this declaration (Lean `… in` form)."""
    out: list[str] = []
    i = d.thm_line - 1
    while i >= 0:
        s = lines[i].strip()
        if not s or s.startswith("--"):
            i -= 1
            continue
        if s.endswith("-/") or s.startswith("/-"):
            if s.startswith("/-") and s.endswith("-/"):
                i -= 1
                continue
            while i >= 0 and not lines[i].strip().startswith("/-"):
                i -= 1
            i -= 1
            continue
        if SCOPED_NEXT.match(lines[i]):
            i -= 1
            continue
        if re.match(r"^(omit|include)\b", s) and re.search(r"\bin\s*$", s):
            nxt = next_theorem_line(lines, i)
            if nxt == d.thm_line:
                out.insert(0, lines[i])
            i -= 1
            continue
        if s.startswith("@["):
            i -= 1
            continue
        break
    return out


Scope = tuple[str, str, int]
MUTUAL_OPEN = re.compile(r"^(\s*)mutual\b")
SECTION_OPEN = re.compile(r"^(\s*)section(?:\s+(\S+))?\s*$")


def scope_stacks(lines: list[str]) -> list[list[Scope]]:
    """Scope stack *before* each line. `mutual` / `section` / `namespace` each push;
    a bare `end` of a `mutual` block must not close an outer namespace."""
    comments = comment_ranges(lines)
    stacks: list[list[Scope]] = []
    stack: list[Scope] = []
    for i, ln in enumerate(lines):
        stacks.append(list(stack))
        if in_comment(i, comments):
            continue
        if MUTUAL_OPEN.match(ln):
            stack.append(("mutual", "", i))
            continue
        m = NAMESPACE_OPEN.match(ln)
        if m:
            stack.append(("ns", m.group(2), i))
            continue
        m = SECTION_OPEN.match(ln)
        if m:
            stack.append(("section", m.group(2) or "", i))
            continue
        if END_LINE.match(ln.rstrip()) and stack:
            stack.pop()
    return stacks


def path_of(stack: list[Scope]) -> list[str]:
    return [name for kind, name, _ in stack if kind in ("ns", "section")]


def scope_in_mutual(stack: list[Scope]) -> bool:
    return any(kind == "mutual" for kind, _, _ in stack)


def namespace_stack_prefix(a: list[str], b: list[str]) -> bool:
    return len(a) <= len(b) and b[: len(a)] == a


def context_before(
    lines: list[str], body_start: int, block_start: int, decls: list[Decl]
) -> list[str]:
    skip = set()
    for d in decls:
        if d.end <= block_start:
            skip.update(range(d.start, d.end))
    stacks = scope_stacks(lines)
    comments = comment_ranges(lines)
    target = stacks[block_start] if block_start < len(stacks) else []
    target_path = path_of(target)
    live_openers = {line for kind, _, line in target if kind in ("ns", "section")}
    out: list[str] = []
    open_binder = False
    binder_depth = 0
    for i in range(body_start, block_start):
        if i in skip or in_comment(i, comments):
            continue
        if open_binder and is_binder_continuation(lines[i], binder_depth):
            out.append(lines[i])
            binder_depth += paren_balance(lines[i])
            if binder_depth < 0:
                binder_depth = 0
            continue
        if lines[i].strip():
            open_binder = False
            binder_depth = 0
        if not is_context_line(lines[i]):
            continue
        s = lines[i].strip()
        if re.match(r"^(omit|include)\b", s) and re.search(r"\bin\s*$", s):
            continue
        # `set_option … in` applies only to the next command. Copied into the
        # ambient context it scopes `open` and the namespace never opens.
        if SCOPED_NEXT.match(lines[i]):
            continue
        if s.endswith("-/") and not s.startswith("/--"):
            continue
        if re.match(r"^\s*end\b", lines[i]):
            continue
        after = stacks[i + 1] if i + 1 < len(stacks) else stacks[i]
        if scope_in_mutual(after) and not scope_in_mutual(target):
            continue
        if not namespace_stack_prefix(path_of(after), target_path):
            continue
        if (NAMESPACE_OPEN.match(lines[i]) or SECTION_OPEN.match(lines[i])) and i not in live_openers:
            continue
        if re.match(r"^\s*attribute\s+\[irreducible\]", lines[i]):
            out.append(
                re.sub(
                    r"^(\s*)attribute\s+\[irreducible\]",
                    r"\1attribute [local irreducible]",
                    lines[i],
                    count=1,
                )
            )
            continue
        out.append(lines[i])
        if lines[i].strip().startswith(("variable", "open", "universe")):
            binder_depth = paren_balance(lines[i])
            open_binder = True
    return out


# Commands whose `in` applies only to the next command. Kept in the ambient
# context they scope `open` / `end` / binder updates and then disappear.
SCOPED_NEXT = re.compile(r"^\s*(?:set_option\b|open\s+scoped\b).*\bin\s*$")


def scoped_next_indices(lines: list[str], block_start: int) -> list[int]:
    """Indices of `set_option … in` / `open scoped … in` that apply to `block_start`."""
    i = block_start - 1
    idxs: list[int] = []
    while i >= 0:
        if not lines[i].strip():
            i -= 1
            continue
        if SCOPED_NEXT.match(lines[i]):
            idxs.append(i)
            i -= 1
            continue
        break
    idxs.reverse()
    return idxs


def scoped_set_options(lines: list[str], block_start: int) -> list[str]:
    """Scoped-to-next commands for this declaration, emitted after durable context."""
    return [lines[i] for i in scoped_next_indices(lines, block_start)]


def filter_theorem_context(
    base_mod: str, ctx: list[str], thm_lines: list[str]
) -> list[str]:
    """Module-specific context fixes after extraction."""
    if base_mod.endswith(".Approximable"):
        text = decl_reference_text(thm_lines)
        needs_ns = any(
            name_referenced_in_text(text, n)
            for n in ("sSupDirected", "le_sSupDirected", "sSupDirected_le")
        )
        if not needs_ns:
            return [
                ln
                for ln in ctx
                if "namespace NeighborhoodSystem" not in ln
                and not re.match(r"^\s*end NeighborhoodSystem\b", ln)
            ]
    return ctx


NAMESPACE_OPEN = re.compile(r"^(\s*)namespace\s+(\S+)")
END_LINE = re.compile(r"^(\s*)end(?:\s+(\S+))?\s*$")


def strip_private_protected(thm_lines: list[str]) -> list[str]:
    out: list[str] = []
    for ln in thm_lines:
        if DECL_HEAD.match(ln):
            ln = re.sub(
                r"^(\s*)((?:private|protected)\s+)+",
                r"\1",
                ln,
            )
        out.append(ln)
    return out


def namespace_close_suffix(lines: list[str]) -> str:
    stacks = scope_stacks(lines)
    stack = stacks[-1] if lines else []
    # `scope_stacks` is the stack *before* each line; apply the last line too.
    if lines:
        last = list(stack)
        ln = lines[-1]
        if not in_comment(len(lines) - 1, comment_ranges(lines)):
            if MUTUAL_OPEN.match(ln):
                last.append(("mutual", "", -1))
            else:
                m = NAMESPACE_OPEN.match(ln)
                if m:
                    last.append(("ns", m.group(2), -1))
                else:
                    m = SECTION_OPEN.match(ln)
                    if m:
                        last.append(("section", m.group(2) or "", -1))
                    elif END_LINE.match(ln.rstrip()) and last:
                        last.pop()
        stack = last
    closers = [(k, n) for k, n, _ in stack if k in ("ns", "section")]
    if not closers:
        return ""
    parts = []
    for kind, name in reversed(closers):
        parts.append(f"end {name}\n" if name else "end\n")
    return "".join(parts)


def strip_doc_comments(text: str) -> str:
    return DOC_BLOCK.sub("", text)


def decl_reference_text(thm_lines: list[str]) -> str:
    """Full declaration block (no doc comments), for cross-theorem name references."""
    return strip_doc_comments("".join(thm_lines))


def decl_dependency_text(thm_lines: list[str]) -> str:
    """Proof / body text only (no declaration header, no doc comments)."""
    text = "".join(thm_lines)
    if ":=" in text:
        text = text.split(":=", 1)[1]
    else:
        for i, ln in enumerate(thm_lines):
            if DECL_HEAD.match(ln):
                text = "".join(thm_lines[i + 1 :])
                break
        else:
            text = ""
    return strip_doc_comments(text)


def name_referenced_in_text(text: str, orig: str) -> bool:
    if re.search(rf"(?<![A-Za-z0-9_'.]){re.escape(orig)}(?![A-Za-z0-9_'])", text):
        return True
    if re.search(rf"\.{re.escape(orig)}\b", text):
        return True
    if "." in orig:
        short = orig.rsplit(".", 1)[-1]
        if short != orig and re.search(rf"\.{re.escape(short)}\b", text):
            return True
    return False


def names_referenced_in_text(
    text: str, candidates: list[tuple[str, str]], exclude: set[str]
) -> list[str]:
    text = strip_doc_comments(text)
    out: list[str] = []
    for orig, safe in candidates:
        if orig in exclude:
            continue
        if name_referenced_in_text(text, orig):
            out.append(safe)
    return out


def paren_balance(s: str) -> int:
    return (
        s.count("(") + s.count("{") + s.count("[")
        - s.count(")") - s.count("}") - s.count("]")
    )


def is_binder_continuation(line: str, depth: int) -> bool:
    """Indented tail of a `variable` / `open` command (unclosed parens or a binder line)."""
    if not (line.startswith(" ") or line.startswith("\t")):
        return False
    s = line.strip()
    if not s or s.startswith("--") or s.startswith("/-"):
        return False
    if DECL_HEAD.match(line) or is_top_level_decl_line(line):
        return False
    if depth > 0:
        return True
    return s[0] in "[({"


def needed_theorem_imports(
    thm_lines: list[str],
    decls: list[Decl],
    current: Decl,
    lines: list[str],
) -> list[str]:
    """Import earlier sibling theorems in this file that the proof refers to."""
    text = decl_reference_text(thm_lines)
    proof = decl_dependency_text(thm_lines)
    wants_simp = bool(re.search(r"\b(simp|simpa|aesop|grind)\b", proof))
    idx = decls.index(current)
    out: list[str] = []
    for d in decls[:idx]:
        header = "".join(lines[d.start : d.thm_line + 1])
        if name_referenced_in_text(text, d.name) or (wants_simp and "@[simp]" in header):
            out.append(safe_module_name(d.name))
    return out


def insert_imports(content: str, new_imports: list[str]) -> str:
    if not new_imports:
        return content
    lines = content.splitlines(keepends=True)
    i = 0
    if i < len(lines) and lines[i].startswith("/-"):
        while i < len(lines):
            i += 1
            if lines[i - 1].strip().endswith("-/"):
                break
    last_import = i
    while i < len(lines) and (IMPORT.match(lines[i]) or lines[i].strip() == ""):
        if IMPORT.match(lines[i]):
            last_import = i + 1
        i += 1
    existing = {m.group(0) for ln in lines if (m := IMPORT.match(ln))}
    to_add = []
    for imp in new_imports:
        line = f"import {imp}\n"
        if line not in existing and line.strip() not in {ln.strip() for ln in lines}:
            to_add.append(line)
    if not to_add:
        return content
    return "".join(lines[:last_import] + to_add + lines[last_import:])


def module_prefix(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    return "DomainTheory." + ".".join(rel.parts)


def restore_from_git(path: Path) -> None:
    rel = path.relative_to(REPO)
    subprocess.run(
        ["git", "checkout", "HEAD", "--", str(rel)],
        cwd=REPO,
        check=True,
        capture_output=True,
    )


def must_stay_in_basic(
    lines: list[str], body_start: int, decls: list[Decl]
) -> set[str]:
    """Theorems that cannot be extracted without import cycles or broken forward refs."""
    by_name = {d.name: d for d in decls}
    stay: set[str] = set()
    private_defs = {
        m.group(3)
        for ln in lines
        if (m := PRIVATE_DECL.match(ln)) and m.group(2) in ("def", "abbrev")
    }
    for d in decls:
        if "@[simp]" in "".join(lines[d.start : d.thm_line + 1]) or decl_is_private(lines, d):
            stay.add(d.name)
            continue
        # A `private def` is invisible from an extracted file. Exposing it clashes
        # when a later module redeclares the same name (Theorem88d/e `encodeBits`).
        text = decl_reference_text(lines[d.start : d.end])
        if any(name_referenced_in_text(text, name) for name in private_defs):
            stay.add(d.name)
    comments = comment_ranges(lines)
    stacks = scope_stacks(lines)
    for i, ln in enumerate(lines):
        if in_comment(i, comments):
            continue
        s = ln.strip()
        if re.match(r"^(include|omit)\b", s) and not re.search(r"\bin\s*$", s):
            inc_path = path_of(stacks[i])
            for d in decls:
                if d.thm_line > i and namespace_stack_prefix(
                    inc_path, path_of(stacks[d.thm_line])
                ):
                    stay.add(d.name)

    def basic_scan_text() -> str:
        skip = set()
        for d in decls:
            if d.name not in stay:
                skip.update(range(d.start, d.end))
        basic_lines = [ln for i, ln in enumerate(lines) if i not in skip]
        return strip_doc_comments("".join(basic_lines[body_start:]))

    changed = True
    while changed:
        changed = False
        scanned = basic_scan_text()
        for d in decls:
            if d.name in stay:
                continue
            if name_referenced_in_text(scanned, d.name):
                stay.add(d.name)
                changed = True
        for name in list(stay):
            thm_lines = lines[by_name[name].start : by_name[name].end]
            for other in decls:
                if other.name in stay:
                    continue
                if name_referenced_in_text(decl_reference_text(thm_lines), other.name):
                    stay.add(other.name)
                    changed = True

    ordered = sorted(decls, key=lambda d: d.start)
    for i, d in enumerate(ordered):
        text = decl_reference_text(lines[d.start : d.end])
        for other in ordered[i + 1 :]:
            if other.name in stay:
                continue
            if name_referenced_in_text(text, other.name):
                stay.add(other.name)

    changed = True
    while changed:
        changed = False
        for name in list(stay):
            text = decl_reference_text(lines[by_name[name].start : by_name[name].end])
            for other in decls:
                if other.name in stay:
                    continue
                if name_referenced_in_text(text, other.name):
                    stay.add(other.name)
                    changed = True

    return stay


def process_file(path: Path, dry_run: bool = False) -> bool:
    if not path.name.endswith(".lean"):
        return False
    subdir = path.with_suffix("")
    if subdir.is_dir() and (subdir / "Basic.lean").exists():
        return False

    text = path.read_text()
    lines = text.splitlines(keepends=True)
    all_decls = parse_decls(lines)
    if not all_decls:
        return False

    header, body_start = split_header(lines)
    base_mod = module_prefix(path)

    stay = must_stay_in_basic(lines, body_start, all_decls)
    decls = [
        d
        for d in all_decls
        if d.name not in stay and not decl_is_private(lines, d)
    ]
    if not decls:
        return False

    basic_body = strip_theorem_blocks(lines, decls)
    basic_body = remove_orphan_doc_comments(basic_body)
    basic_body = strip_orphan_omit_include(basic_body)
    basic_body = remove_redundant_private_theorem_blocks(basic_body, header)
    expose_private_decls(basic_body, decls, lines)
    if base_mod.endswith(".InformationSystems.Approximable"):
        for i, ln in enumerate(basic_body):
            if re.match(r"^\s*private\s+theorem\s+singleton_funion_eq\b", ln):
                basic_body[i] = re.sub(r"^(\s*)private\s+", r"\1", ln, count=1)
    basic_body = cleanup_basic_tail(basic_body)
    basic_body = strip_irreducible_attributes(basic_body)
    while basic_body and basic_body[-1].strip() == "":
        basic_body.pop()

    thm_files: list[tuple[str, str]] = []

    for d in decls:
        thm_lines_raw = lines[d.start : d.end]
        ctx = filter_theorem_context(
            base_mod,
            context_before(lines, body_start, d.start, decls),
            thm_lines_raw,
        )
        ctx = ctx + omit_include_for_decl(lines, d)
        scoped = scoped_set_options(lines, d.start)
        thm_lines = remove_orphan_doc_comments(thm_lines_raw)
        thm_lines = strip_private_protected(thm_lines)
        while thm_lines and thm_lines[-1].strip().startswith("omit "):
            thm_lines.pop()
        safe = safe_module_name(d.name)
        imports = [ln for ln in header if IMPORT.match(ln)]
        extra = [f"import {base_mod}.Basic\n"]
        seen: set[str] = set()
        for psafe in needed_theorem_imports(thm_lines, decls, d, lines):
            if psafe == safe or psafe in seen:
                continue
            extra.append(f"import {base_mod}.{psafe}\n")
            seen.add(psafe)
        body = (
            "".join(ctx)
            + "".join(scoped)
            + "".join(thm_lines)
            + namespace_close_suffix(ctx + scoped + thm_lines)
        )
        content = (
            COPYRIGHT
            + "\n"
            + "".join(imports)
            + "".join(extra)
            + "\n"
            + body
        )
        if not content.endswith("\n"):
            content += "\n"
        thm_files.append((safe, content))

    basic_content = "".join(basic_body)
    if not basic_content.endswith("\n"):
        basic_content += "\n"

    agg_imports = [f"import {base_mod}.Basic\n"]
    for name, _ in thm_files:
        agg_imports.append(f"import {base_mod}.{name}\n")
    agg_content = COPYRIGHT + "\n" + "".join(agg_imports)

    if dry_run:
        print(f"would split {path.relative_to(ROOT)} -> {len(decls)} theorems")
        return True

    subdir.mkdir(exist_ok=True)
    (subdir / "Basic.lean").write_text(basic_content)
    for name, content in thm_files:
        (subdir / f"{name}.lean").write_text(content)
    path.write_text(agg_content)
    return True


def main() -> int:
    dry = "--dry-run" in sys.argv
    force = "--force" in sys.argv
    n = 0
    for path in sorted(ROOT.rglob("*.lean")):
        rel = path.relative_to(ROOT)
        if len(rel.parts) != 2:
            continue
        if path.name == "Basic.lean":
            continue
        subdir = path.parent / path.stem
        if subdir.is_dir() and (subdir / "Basic.lean").exists():
            if not force:
                continue
            if not dry:
                shutil.rmtree(subdir)
                restore_from_git(path)

        if process_file(path, dry_run=dry):
            n += 1
    print(f"split {n} files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
