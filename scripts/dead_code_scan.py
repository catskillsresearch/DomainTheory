#!/usr/bin/env python3
"""Report Lean modules imported only by DomainTheory.lean (barrel-only candidates).

Excludes paper-labelled modules (Factoid/Theorem/Proposition/proposition/eq_/lemma_/corollary_/…).
See DomainTheory/dead_code_candidates.md for the latest report.
"""

from __future__ import annotations

import argparse
import re
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DT = ROOT / "DomainTheory"
REPORT = DT / "dead_code_candidates.md"
BARREL = ROOT / "DomainTheory.lean"

IMPORT = re.compile(r"^(?:public\s+|private\s+|meta\s+)?import\s+(?:all\s+)?(\S+)\s*$")
LEAN_IMPORT_MD = re.compile(r'@import\s+"([^"]+\.lean)"')
PAPER_STEM = re.compile(
    r"(?i)^(factoid|theorem|proposition|corollary|lemma|eq_)"
)
PAPER_PATH = re.compile(
    r"(?i)(Factoid\d+|Theorem\d+|Proposition\d+|Exercise|Example)[_/]"
)


def module_of(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def direct_imports(path: Path) -> list[str]:
    out: list[str] = []
    for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        m = IMPORT.match(line.strip())
        if m:
            out.append(m.group(1))
    return out


def is_excluded_paper(path: Path) -> bool:
    if PAPER_STEM.match(path.stem):
        return True
    joined = "/".join(path.relative_to(DT).parts)
    return bool(PAPER_PATH.search(joined))


@dataclass(frozen=True)
class Candidate:
    chapter: str
    rel: str
    module: str
    in_notes: bool
    note_refs: int
    lines: int


def load_importers(modules: dict[str, Path]) -> dict[str, set[str]]:
    importers: dict[str, set[str]] = {m: set() for m in modules}
    for mod, path in modules.items():
        for imp in direct_imports(path):
            if imp in modules:
                importers[imp].add(mod)
    return importers


def md_note_refs(modules: dict[str, Path]) -> dict[str, int]:
    counts: dict[str, int] = defaultdict(int)
    for md in DT.rglob("*.md"):
        text = md.read_text(encoding="utf-8", errors="ignore")
        for m in LEAN_IMPORT_MD.finditer(text):
            lean = (md.parent / m.group(1).split("#")[0]).resolve()
            if lean.is_file():
                mod = module_of(lean)
                if mod in modules:
                    counts[mod] += 1
    return counts


def collect_candidates() -> list[Candidate]:
    modules = {module_of(p): p for p in DT.rglob("*.lean")}
    importers = load_importers(modules)
    barrel_mod = module_of(BARREL)
    barrel_imports = set(direct_imports(BARREL))
    note_refs = md_note_refs(modules)

    rows: list[Candidate] = []
    for mod, path in sorted(modules.items(), key=lambda x: str(x[1])):
        if mod not in barrel_imports:
            continue
        if importers[mod] - {barrel_mod}:
            continue
        if is_excluded_paper(path):
            continue
        rel = path.relative_to(ROOT)
        chapter = rel.parts[1] if len(rel.parts) > 2 else "?"
        nref = note_refs.get(mod, 0)
        rows.append(
            Candidate(
                chapter=chapter,
                rel=str(rel).replace("\\", "/"),
                module=mod,
                in_notes=nref > 0,
                note_refs=nref,
                lines=len(path.read_text(encoding="utf-8", errors="ignore").splitlines()),
            )
        )
    return rows


def triage_section(candidates: list[Candidate]) -> str:
    """Human review guidance (not auto-applied)."""
    dt_no_note = [
        c for c in candidates if c.chapter == "DataTypesAsLattices" and not c.in_notes
    ]
    by_sub: Counter[str] = Counter()
    for c in dt_no_note:
        parts = Path(c.rel).parts
        sub = parts[2] if len(parts) > 3 else "?"
        by_sub[sub] += 1
    dt_lines = [
        "",
        "#### DataTypesAsLattices — 54 modules not in any note (by subfolder)",
        "",
        "| Subfolder | Count | Suggested action |",
        "|-----------|------:|------------------|",
    ]
    for sub, n in sorted(by_sub.items(), key=lambda x: (-x[1], x[0])):
        dt_lines.append(
            f"| `{sub}/` | {n} | **delete** or **fold** into parent if split was file-size only |"
        )
    dt_block = "\n".join(dt_lines)

    return f"""\
## Triage guide (manual review)

Actions: **delete** (unused + redundant), **merge** (into an importing sibling module),
**wire** (call from proofs), **keep** (notes/PDF or Palomar barrel only).

### ContinuousLattice

The former barrel-only dozen (Sierpiński conjunction, `orderIso_wayBelow_iff`, note-only FunctionSpaces/Milner/Specialization splits) was **deleted**; proofs use sibling modules (`orderIso_wayBelow`, `*_apply`, `isOpen_iff_scottOpen`, etc.).

### DataTypesAsLattices (64)

- **54 with no `.md` cite:** see subfolder table below.
- **10 with notes** (`Lambda/` examples, `Retracts/inter_const_isScottContinuous`, `Functionality/Hcomb_more`): **keep** for narrative unless merged into numbered notes.
{dt_block}

### NeighbourhoodSystems (6 `*_lock.lean`)

| File | Suggested action | Rationale |
|------|------------------|-----------|
| `ASharp_lock`, `CoupledFixedPoints_lock`, `EmbeddingsIntoU_lock`, `ExampleC_le_B_lock`, `FixOp_lock`, `BooleanAlgebraFilters_more` | **keep** | Large cycle-break / registration modules; mermaid shows `*_more → *_lock`. Not dead—barrel-only by design. |

### BridgeTheorems

Bridge aggregator modules (`Equivalence.lean`, `WorkedExampleSExpr.lean`) were removed; leaf imports live in `DomainTheory.lean`. SExpr content remains under `WorkedExampleSExpr/` and in bridge notes.

### InformationSystems (1)

| File | Suggested action | Rationale |
|------|------------------|-----------|
| `SomeDomainEquations/DomainEquation.lean` | **keep** or **merge** into Factoid82 cluster | Cited in notes; may be a standalone def for the domain-equation section. |
"""  # noqa: E501


def render_report(candidates: list[Candidate]) -> str:
    by_ch = Counter(c.chapter for c in candidates)
    in_notes = sum(1 for c in candidates if c.in_notes)
    no_notes = len(candidates) - in_notes

    lines = [
        "# Dead code candidates (barrel-only modules)",
        "",
        "Generated by `scripts/dead_code_scan.py`. Re-run after import changes.",
        "",
        "## Scan rules",
        "",
        "1. Module is imported in [`DomainTheory.lean`](../DomainTheory.lean).",
        "2. No other `DomainTheory/**/*.lean` file imports it.",
        "3. **Excluded:** stems `factoid*`, `theorem*`, `proposition*`, `corollary*`, "
        "`lemma*`, `eq_*`; paths under `FactoidNN` / `TheoremNN` / `PropositionNN`; "
        "`Exercise` / `Example` segments.",
        "",
        "## Summary",
        "",
        f"- **Total candidates:** {len(candidates)}",
        f"- **Cited in at least one `.md` note:** {in_notes}",
        f"- **Not in any note `@import`:** {no_notes}",
        "",
        "| Chapter | Count | In notes | Not in notes |",
        "|---------|------:|---------:|-------------:|",
    ]
    for ch in sorted(by_ch, key=lambda c: (-by_ch[c], c)):
        grp = [c for c in candidates if c.chapter == ch]
        lines.append(
            f"| {ch} | {len(grp)} | {sum(1 for c in grp if c.in_notes)} | "
            f"{sum(1 for c in grp if not c.in_notes)} |"
        )
    lines.append("")
    lines.append("## Candidates by chapter")
    lines.append("")

    cur: str | None = None
    for c in candidates:
        if c.chapter != cur:
            if cur is not None:
                lines.append("")
            cur = c.chapter
            lines.append(f"### {cur}")
            lines.append("")
            lines.append("| File | In notes | Lines |")
            lines.append("|------|----------|------:|")
        notes = "yes" if c.in_notes else "no"
        lines.append(f"| [{c.rel}]({c.rel}) | {notes} | {c.lines} |")
    lines.append("")

    lines.append(triage_section(candidates))
    return "\n".join(lines)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--write",
        action="store_true",
        help=f"Write {REPORT.relative_to(ROOT)}",
    )
    ap.add_argument(
        "--print",
        action="store_true",
        help="Print report to stdout",
    )
    args = ap.parse_args()
    if not args.write and not args.print:
        args.print = True

    candidates = collect_candidates()
    report = render_report(candidates)

    if args.print:
        print(report)
    if args.write:
        REPORT.write_text(report, encoding="utf-8")
        print(f"wrote {REPORT.relative_to(ROOT)} ({len(candidates)} candidates)")


if __name__ == "__main__":
    main()
