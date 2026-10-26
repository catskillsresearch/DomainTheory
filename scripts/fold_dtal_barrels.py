#!/usr/bin/env python3
"""Fold DataTypesAsLattices topic barrels into DomainTheory.lean.

Retarget every barrel import to the leaf modules that file actually *names*
(via the public-import closure of those barrels), then delete the barrels.
"""
from __future__ import annotations

import re
from collections import defaultdict, deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DTAL = ROOT / "DomainTheory" / "DataTypesAsLattices"
DOMAIN_THEORY_LEAN = ROOT / "DomainTheory.lean"

BARREL_NAMES = {p.stem for p in DTAL.glob("*.lean") if p.is_file()}
BARREL_MODS = {f"DomainTheory.DataTypesAsLattices.{b}" for b in BARREL_NAMES}
BARREL_PATHS = {DTAL / f"{b}.lean" for b in BARREL_NAMES}

IMP_RE = re.compile(r"^(?P<pub>public\s+)?import\s+(?P<mod>\S+)\s*$", re.M)
DECL_RE = re.compile(
    r"(?m)^(?:(?:noncomputable|protected|private|scoped|local)\s+)*"
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:noncomputable|protected|private|scoped|local)\s+)*"
    r"(?:def|theorem|lemma|example|abbrev|structure|class|inductive|opaque|axiom|alias)\s+"
    r"(?P<name>[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)"
)
INST_NAMED_RE = re.compile(
    r"(?m)^(?:(?:noncomputable|protected|private|scoped|local)\s+)*"
    r"(?:@\[[^\]]*\]\s*)*"
    r"instance\s+(?P<name>[A-Za-z_][\w']*)\b"
)
IDENT_RE = re.compile(r"\b([A-Za-z_][\w']*)\b")

SKIP_NAMES = {
    "a", "b", "c", "d", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q",
    "r", "s", "t", "u", "v", "w", "x", "y", "z",
    "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P",
    "Q", "R", "S", "T", "U", "V", "W", "X", "Y",
    "by", "of", "if", "then", "else", "have", "show", "let", "fun", "where",
    "with", "for", "in", "do", "pure", "return", "open", "set", "Set", "Type",
    "Prop", "Sort", "True", "False", "And", "Or", "Not", "Eq", "Iff", "Exists",
    "Nat", "Int", "Bool", "List", "Option", "Sum", "Prod", "Unit", "Empty",
    "id", "sorry", "rfl", "trivial", "simp", "rw", "exact", "apply", "intro",
    "constructor", "cases", "induction", "refine", "use", "obtain", "rcases",
    "ext", "congr", "calc", "suffices", "change", "convert", "specialize",
    "module", "namespace", "section", "end", "variable", "universe", "noncomputable",
    "public", "private", "protected", "scoped", "local", "import", "inductive",
    "structure", "class", "theorem", "lemma", "def", "abbrev", "instance", "axiom",
    "opaque", "alias", "example", "mutual", "partial", "unsafe",
    "le", "re", "ub",
}
ALLOW_SHORT = {"e", "Z", "Ea", "HF", "Nk", "RE"}


def mod_of_path(path: Path) -> str:
    rel = path.relative_to(ROOT / "DomainTheory")
    return "DomainTheory." + ".".join(rel.with_suffix("").parts)


def path_of_mod(mod: str) -> Path | None:
    if not mod.startswith("DomainTheory."):
        return None
    return ROOT / "DomainTheory" / Path(*mod.split(".")[1:]).with_suffix(".lean")


def parse_imports(text: str) -> list[tuple[bool, str, int, int]]:
    return [
        (bool(m.group("pub")), m.group("mod"), m.start(), m.end())
        for m in IMP_RE.finditer(text)
    ]


def direct_imports(mod: str) -> list[str]:
    path = path_of_mod(mod)
    if path is None or not path.is_file():
        return []
    return [m for _, m, _, _ in parse_imports(path.read_text(errors="ignore"))]


def load_module_imports() -> dict[str, list[str]]:
    """All DomainTheory.DataTypesAsLattices.* modules -> their import lists."""
    result: dict[str, list[str]] = {}
    for path in DTAL.rglob("*.lean"):
        mod = mod_of_path(path)
        result[mod] = [m for _, m, _, _ in parse_imports(path.read_text(errors="ignore"))]
    return result


def closure(roots: set[str], imports: dict[str, list[str]]) -> list[str]:
    """BFS public/regular import closure; DomainTheory modules only for ordering leaves;
    Mathlib modules included when directly imported."""
    seen: set[str] = set()
    ordered: list[str] = []
    q: deque[str] = deque(sorted(roots))
    while q:
        mod = q.popleft()
        if mod in seen:
            continue
        seen.add(mod)
        # Skip barrels in the ordered leaf list, but still traverse them.
        is_barrel = mod in BARREL_MODS
        if not is_barrel:
            ordered.append(mod)
        for child in imports.get(mod, direct_imports(mod)):
            if child.startswith("DomainTheory.DataTypesAsLattices.") or child.startswith("Mathlib."):
                if child not in seen:
                    q.append(child)
    return ordered


def index_declarations(mods: set[str]) -> dict[str, set[str]]:
    name_to_mods: dict[str, set[str]] = defaultdict(set)
    for mod in mods:
        path = path_of_mod(mod)
        if path is None or not path.is_file():
            continue
        text = path.read_text(errors="ignore")
        for m in DECL_RE.finditer(text):
            raw = m.group("name")
            base = raw.split(".")[0]
            if base in SKIP_NAMES and base not in ALLOW_SHORT:
                continue
            if len(base) <= 1 and base not in ALLOW_SHORT:
                continue
            name_to_mods[base].add(mod)
            if "." in raw:
                name_to_mods[raw].add(mod)
        for m in INST_NAMED_RE.finditer(text):
            name = m.group("name")
            if name in SKIP_NAMES and name not in ALLOW_SHORT:
                continue
            name_to_mods[name].add(mod)
    return name_to_mods


def file_idents(text: str) -> set[str]:
    body = IMP_RE.sub("", text)
    body = re.sub(r"/--.*?-/", " ", body, flags=re.S)
    body = re.sub(r"/-.*?-/", " ", body, flags=re.S)
    body = re.sub(r"--.*?$", " ", body, flags=re.M)
    return set(IDENT_RE.findall(body))


def used_modules_for_file(
    text: str,
    reachable: set[str],
    reachable_ordered: list[str],
    name_to_mods: dict[str, set[str]],
    self_mod: str,
) -> list[str]:
    idents = file_idents(text)
    needed: set[str] = set()
    for name, mods in name_to_mods.items():
        if name not in idents:
            continue
        if name in SKIP_NAMES and name not in ALLOW_SHORT:
            continue
        for mod in mods:
            if mod in reachable and mod != self_mod:
                needed.add(mod)

    topo_tokens = {
        "TopologicalSpace", "IsOpen", "IsClosed", "Continuous", "IsCompact",
        "nhds", "closure", "interior", "inducing", "Induced",
        "IsScottOpen", "IsScottContinuous", "basicNhhd", "memOpen", "scottUnion",
    }
    if idents & topo_tokens:
        for m in reachable_ordered:
            if m.startswith("Mathlib.") and ("Topology" in m or "Order" in m):
                needed.add(m)
    if idents & {"REPred", "Computable", "Primrec", "Part"}:
        for m in reachable_ordered:
            if m.startswith("Mathlib.") and "Computability" in m:
                needed.add(m)

    ordered = [m for m in reachable_ordered if m in needed]
    for m in sorted(needed):
        if m not in ordered:
            ordered.append(m)
    return ordered


def remove_spans(text: str, spans: list[tuple[int, int]]) -> str:
    for start, end in sorted(spans, reverse=True):
        text = text[:start] + text[end:]
    return text


def rewrite_consumer(
    path: Path,
    barrel_closure: dict[str, list[str]],
    name_to_mods: dict[str, set[str]],
) -> tuple[bool, int]:
    text = path.read_text()
    imps = parse_imports(text)
    barrel_hits = [(is_pub, mod, start, end) for is_pub, mod, start, end in imps if mod in BARREL_MODS]
    if not barrel_hits:
        return False, 0

    use_public = any(is_pub for is_pub, _, _, _ in barrel_hits)
    self_mod = mod_of_path(path)

    # Union of closures of imported barrels
    ordered: list[str] = []
    seen: set[str] = set()
    for _, mod, _, _ in barrel_hits:
        short = mod.rsplit(".", 1)[-1]
        for m in barrel_closure[short]:
            if m not in seen:
                seen.add(m)
                ordered.append(m)

    needed = used_modules_for_file(text, seen, ordered, name_to_mods, self_mod)
    already = {mod for _, mod, _, _ in imps if mod not in BARREL_MODS}
    to_add = [m for m in needed if m not in already and m != self_mod]

    spans = []
    first_start = barrel_hits[0][2]
    for _, _, start, end in barrel_hits:
        eol = text.find("\n", end)
        spans.append((start, eol + 1 if eol != -1 else len(text)))
        first_start = min(first_start, start)

    new_text = remove_spans(text, spans)
    removed_before = sum(end - start for start, end in spans if end <= first_start)
    insert_at = first_start - removed_before

    if to_add:
        prefix = "public import " if use_public else "import "
        block = "".join(f"{prefix}{m}\n" for m in to_add)
        new_text = new_text[:insert_at] + block + new_text[insert_at:]

    if new_text != text:
        path.write_text(new_text)
        return True, len(to_add)
    return False, len(to_add)


def all_dtal_leaves_for_root(imports: dict[str, list[str]]) -> list[str]:
    """Closure of every barrel, DomainTheory leaves only, stable order."""
    return [
        m
        for m in closure(BARREL_MODS, imports)
        if m.startswith("DomainTheory.DataTypesAsLattices.")
    ]


def rewrite_domain_theory_lean(leaf_mods: list[str]) -> None:
    text = DOMAIN_THEORY_LEAN.read_text()
    lines = text.splitlines(keepends=True)
    out: list[str] = []
    i = 0
    replaced = False
    dtal_barrel_line = re.compile(
        r"^import\s+DomainTheory\.DataTypesAsLattices\.("
        + "|".join(map(re.escape, sorted(BARREL_NAMES)))
        + r")\s*$"
    )
    while i < len(lines):
        if dtal_barrel_line.match(lines[i].rstrip("\n")):
            if not replaced:
                seen: set[str] = set()
                for mod in leaf_mods:
                    if mod in seen:
                        continue
                    seen.add(mod)
                    out.append(f"import {mod}\n")
                replaced = True
            i += 1
            continue
        out.append(lines[i])
        i += 1
    if not replaced:
        raise SystemExit("DomainTheory.lean: no DTAL barrel imports found to replace")
    DOMAIN_THEORY_LEAN.write_text("".join(out))


def main() -> None:
    imports = load_module_imports()
    barrel_closure = {
        b: closure({f"DomainTheory.DataTypesAsLattices.{b}"}, imports) for b in BARREL_NAMES
    }
    leaf_mods = all_dtal_leaves_for_root(imports)
    print(f"barrels: {sorted(BARREL_NAMES)}")
    print(f"DTAL leaves for DomainTheory.lean: {len(leaf_mods)}")
    for b in sorted(BARREL_NAMES):
        print(f"  closure({b}): {len(barrel_closure[b])}")

    # Index declarations from every DomainTheory module that appears in any closure
    all_reachable = set().union(*(set(v) for v in barrel_closure.values()))
    dtal_reachable = {m for m in all_reachable if m.startswith("DomainTheory.")}
    name_to_mods = index_declarations(dtal_reachable)
    print(f"indexed names: {len(name_to_mods)}")
    print(f"  Pomega defined in: {sorted(name_to_mods.get('Pomega', []))}")
    print(f"  e defined in: {sorted(name_to_mods.get('e', []))}")

    consumers = []
    for path in sorted((ROOT / "DomainTheory").rglob("*.lean")):
        if path in BARREL_PATHS:
            continue
        if any(mod in BARREL_MODS for _, mod, _, _ in parse_imports(path.read_text(errors="ignore"))):
            consumers.append(path)
    print(f"consumers: {len(consumers)}")

    changed = 0
    zero = 0
    for path in consumers:
        ok, n = rewrite_consumer(path, barrel_closure, name_to_mods)
        if ok:
            changed += 1
        if n == 0:
            zero += 1
    print(f"rewrote: {changed}; zero inferred leaf imports: {zero}")

    rewrite_domain_theory_lean(leaf_mods)
    print("updated DomainTheory.lean")

    for p in BARREL_PATHS:
        p.unlink()
    print(f"deleted {len(BARREL_PATHS)} barrels")

    leftover = []
    for path in (ROOT / "DomainTheory").rglob("*.lean"):
        for _, mod, _, _ in parse_imports(path.read_text(errors="ignore")):
            if mod in BARREL_MODS:
                leftover.append((path, mod))
    print("leftover barrel imports:" if leftover else "no leftover barrel imports", len(leftover) if leftover else "")

    for sample in [
        DTAL / "Lambda" / "Comb.lean",
        DTAL / "Lambda" / "succSet.lean",
        DTAL / "Embedding" / "extend.lean",
        DTAL / "Embedding" / "theorem_1_5.lean",
    ]:
        print(f"\n--- {sample.relative_to(ROOT)} ---")
        print("".join(sample.read_text().splitlines(True)[:20]))


if __name__ == "__main__":
    main()
