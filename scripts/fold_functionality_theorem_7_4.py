#!/usr/bin/env python3
"""Merge Theorem 7.4 Functionality leaves into PascalCase parents."""
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from fold_dtal_companions import (  # noqa: E402
    rebuild_parent,
    rewrite_imports_and_refs,
    IMP_RE,
)

FUNC = ROOT / "DomainTheory" / "DataTypesAsLattices" / "Functionality"
MOD = "DomainTheory.DataTypesAsLattices.Functionality"
NS = "namespace DomainTheory.DataTypesAsLattices"


def seed(path: Path, pref: str, imports: list[str], core: str = "") -> None:
    imps = "\n".join(f"public import {m}" for m in imports)
    path.write_text(
        f"module\n\n{imps}\n\n"
        "@[expose] public section\n\n"
        f"{NS}\n\n"
        f"{core}\n"
        f"namespace {pref}\n\nend {pref}\n\n"
        "end DomainTheory.DataTypesAsLattices\n"
    )


def merge(pref: str, companions: list[tuple[str, str]], *, as_more: bool = False) -> tuple[dict[str, str], list[tuple[str, str]]]:
    deleted: dict[str, str] = {}
    renames: list[tuple[str, str]] = []
    target = f"{pref}_more" if as_more else pref
    paths, rns = rebuild_parent(FUNC, pref, companions, as_more=as_more)
    for p in paths:
        deleted[f"{MOD}.{p.stem}"] = f"{MOD}.{target}"
    renames.extend(rns)
    return deleted, renames


def extra_renames(pairs: list[tuple[str, str]]) -> list[tuple[str, str]]:
    return pairs


def main() -> None:
    all_deleted: dict[str, str] = {}
    all_renames: list[tuple[str, str]] = []

    # --- PairSeq ---
    if not (FUNC / "PairSeq.lean").exists():
        seed(
            FUNC / "PairSeq.lean",
            "PairSeq",
            ["DomainTheory.DataTypesAsLattices.Retracts.pairSeq"],
        )
    d, r = merge(
        "PairSeq",
        [
            ("pairSeq_app_zero", "app_zero"),
            ("pairSeq_app_one", "app_one"),
            ("pairSeq_inj", "inj"),
            ("pairSeq_isScottContinuous_left", "isScottContinuous_left"),
            ("pairSeq_isScottContinuous_right", "isScottContinuous_right"),
        ],
    )
    all_deleted.update(d)
    all_renames.extend(r)
    all_renames.extend(
        [
            ("pairSeq_app_zero", "PairSeq.app_zero"),
            ("pairSeq_app_one", "PairSeq.app_one"),
            ("pairSeq_inj", "PairSeq.inj"),
            ("pairSeq_isScottContinuous_left", "PairSeq.isScottContinuous_left"),
            ("pairSeq_isScottContinuous_right", "PairSeq.isScottContinuous_right"),
        ]
    )

    # --- ContinuityHelpers ---
    if not (FUNC / "ContinuityHelpers.lean").exists():
        seed(FUNC / "ContinuityHelpers.lean", "ContinuityHelpers", [])
    d, r = merge(
        "ContinuityHelpers",
        [
            ("continuous_on_diag", "on_diag"),
            ("continuous_tuple", "tuple"),
            ("continuous_nary", "nary"),
        ],
    )
    all_deleted.update(d)
    all_renames.extend(r)
    all_renames.extend(
        [
            ("continuous_on_diag", "ContinuityHelpers.on_diag"),
            ("continuous_tuple", "ContinuityHelpers.tuple"),
            ("continuous_nary", "ContinuityHelpers.nary"),
        ]
    )

    # --- EncodeExp cluster (defs stay at root in encodeExp.lean) ---
    d, r = merge("encodeExp", [("encodeExp_typed", "typed")])
    all_deleted.update(d)
    all_renames.extend(r)
    all_renames.append(("encodeExp_typed", "encodeExp.typed"))

    # expTag, expPayload, eraseTag → encodeExp namespaces (manual merge via rebuild on encodeExp)
    # Move defs from leaf files into encodeExp.lean root first if needed
    for leaf, ns in [("expTag", "expTag"), ("expPayload", "expPayload"), ("eraseTag", "eraseTag")]:
        path = FUNC / f"{leaf}.lean"
        if not path.exists():
            continue
        text = path.read_text()
        parent = FUNC / "encodeExp.lean"
        pt = parent.read_text()
        if f"def {leaf}" in pt:
            path.unlink()
            all_deleted[f"{MOD}.{leaf}"] = f"{MOD}.encodeExp"
            all_renames.append((leaf, f"encodeExp.{leaf}" if ns == "expTag" else leaf))
            continue
        body_start = text.find(NS)
        body = text[body_start + len(NS) + 1 :]
        body = body.replace("end DomainTheory.DataTypesAsLattices", "").strip()
        # strip duplicate namespace for eraseTag
        if f"namespace {ns}" in body:
            import re

            body = re.sub(
                rf"namespace {ns}\s*\n(.*?)\nend {ns}\s*",
                rf"namespace {ns}\n\1\nend {ns}\n",
                body,
                flags=re.S,
            )
        insert = "\n" + body + "\n"
        pt = pt.replace(
            "\nend DomainTheory.DataTypesAsLattices\n",
            insert + "\nend DomainTheory.DataTypesAsLattices\n",
        )
        for mod in [m.group("mod") for m in IMP_RE.finditer(text)]:
            if mod not in pt and mod != f"{MOD}.{leaf}":
                pt = pt.replace(
                    "public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm\n",
                    f"public import {mod}\n"
                    "public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm\n",
                )
        parent.write_text(pt)
        path.unlink()
        all_deleted[f"{MOD}.{leaf}"] = f"{MOD}.encodeExp"
        if leaf == "expTag":
            all_renames.append(("expTag", "encodeExp.expTag"))
        elif leaf == "expPayload":
            all_renames.append(("expPayload", "encodeExp.expPayload"))

    # --- Zcomb eq (7.18)–(7.19) ---
    d, r = merge(
        "Zcomb",
        [
            ("eq_7_18_eq", "eq_7_18_eq"),
            ("eq_7_18_ne", "eq_7_18_ne"),
            ("eq_7_19", "eq_7_19"),
        ],
    )
    all_deleted.update(d)
    all_renames.extend(r)
    for name in ("eq_7_18_eq", "eq_7_18_ne", "eq_7_19"):
        all_renames.append((name, f"Zcomb.{name}"))

    # --- PlotkinHelpers (finite / predSet iterate) ---
    if not (FUNC / "PlotkinHelpers.lean").exists():
        seed(FUNC / "PlotkinHelpers.lean", "PlotkinHelpers", [])
    d, r = merge(
        "PlotkinHelpers",
        [
            ("predSet_iterate_ofNat", "predSet_iterate_ofNat"),
            ("predSet_iterate_self", "predSet_iterate_self"),
            ("predSet_iterate_expTag_isScottContinuous", "predSet_iterate_expTag_isScottContinuous"),
            ("normalized_finite_app", "normalized_finite_app"),
            ("normalized_finite_fresh_app", "normalized_finite_fresh_app"),
            ("finite_sigma_plain_app", "finite_sigma_plain_app"),
            ("finite_sigma_union_app", "finite_sigma_union_app"),
        ],
    )
    all_deleted.update(d)
    all_renames.extend(r)
    for stem in [
        "predSet_iterate_ofNat",
        "predSet_iterate_self",
        "predSet_iterate_expTag_isScottContinuous",
        "normalized_finite_app",
        "normalized_finite_fresh_app",
        "finite_sigma_plain_app",
        "finite_sigma_union_app",
    ]:
        all_renames.append((stem, f"PlotkinHelpers.{stem}"))

    # Fix Z.lean import continuous_tuple → ContinuityHelpers
    z_path = FUNC / "Z.lean"
    if z_path.exists():
        zt = z_path.read_text()
        zt = zt.replace(
            "Functionality.continuous_tuple",
            "Functionality.ContinuityHelpers",
        )
        zt = zt.replace("continuous_tuple", "ContinuityHelpers.tuple")
        z_path.write_text(zt)

    n = rewrite_imports_and_refs(all_deleted, all_renames)
    print(f"rewrote {n} files; {len(all_deleted)} deleted modules")

    dt = (ROOT / "DomainTheory.lean").read_text()
    for mod in sorted(all_deleted, key=len, reverse=True):
        import re

        dt = re.sub(rf"^import\s+{re.escape(mod)}\s*\n", "", dt, flags=re.M)
    parents = sorted(set(all_deleted.values()))
    for parent in parents:
        if f"import {parent}\n" not in dt:
            # append before Functionality section end — simple append
            if f"import {parent}" not in dt:
                dt += f"import {parent}\n"
    (ROOT / "DomainTheory.lean").write_text(dt)


if __name__ == "__main__":
    main()
