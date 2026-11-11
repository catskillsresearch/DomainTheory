#!/usr/bin/env bash
# Reproduce the repository-side mechanical checks needed before Palomar submission.
set -euo pipefail
cd "$(dirname "$0")/.."

step() {
  printf '\n== %s ==\n' "$1"
}

step "Validate Comparator configuration"
python3 - <<'PY'
import json

with open("comparator.json", encoding="utf-8") as f:
    cfg = json.load(f)

required = ("challenge_module", "solution_module", "theorem_names",
            "definition_names", "permitted_axioms")
missing = [key for key in required if key not in cfg]
if missing:
    raise SystemExit(f"Missing comparator keys: {', '.join(missing)}")

names = cfg["theorem_names"] + cfg["definition_names"]
duplicates = sorted({name for name in names if names.count(name) > 1})
if duplicates:
    raise SystemExit(f"Duplicate Comparator names: {', '.join(duplicates)}")
print(f"OK: {len(cfg['theorem_names'])} theorem targets and "
      f"{len(cfg['definition_names'])} definition targets.")
PY

step "Match formalization.yaml vendor revisions to FROZEN.txt"
python3 - <<'PY'
import re

frozen = open("vendor/FROZEN.txt", encoding="utf-8").read()
yaml = open("formalization.yaml", encoding="utf-8").read()
revs = re.findall(
    r"vendor/(scott(?:19\d{2}|_models))\n(?:  .*\n)*?  rev:\s+(\S+)", frozen
)
if len(revs) != 5:
    raise SystemExit(f"Could not parse five vendor revisions from FROZEN.txt: {revs}")
missing = []
for name, rev in revs:
    if f"/tree/{rev}" not in yaml:
        missing.append(f"{name} {rev}")
if missing:
    raise SystemExit(
        "formalization.yaml is missing related_formalizations "
        f"tree URLs for: {', '.join(missing)}"
    )
print("OK: related_formalizations revisions match vendor/FROZEN.txt.")
PY

step "Require explicit Challenge names for compared instances"
python3 - <<'PY'
import json
import re

with open("comparator.json", encoding="utf-8") as f:
    cfg = json.load(f)
src = open("Challenge.lean", encoding="utf-8").read()
missing = []
for name in cfg["theorem_names"] + cfg["definition_names"]:
    short = name.rsplit(".", 1)[-1]
    if not short.startswith("inst"):
        continue
    if not re.search(rf"\binstance\s+{re.escape(short)}\b", src):
        missing.append(name)
if missing:
    raise SystemExit(
        "Challenge.lean is missing explicit instance names for: "
        + ", ".join(missing)
    )
print("OK: compared instances have explicit Challenge names.")
PY

step "Narrative / attribution consistency (formalization.yaml)"
python3 - <<'PY'
import json
import re
from pathlib import Path

cfg = json.loads(Path("comparator.json").read_text(encoding="utf-8"))
yaml = Path("formalization.yaml").read_text(encoding="utf-8")
prov = Path("PROVENANCE.md").read_text(encoding="utf-8")
errors = []

# 1. Author contributions for all four co-authors
contrib_blob = yaml + "\n" + prov
required_people = [
    ("Lars Warren Ericson", ("formalization engineer", "Lean 4", "repository assembly")),
    ("Dana", ("source mathematics", "sponsorship", "scope")),
    ("D'Silva", ("pre-submission", "initiation", "formatting")),
    ("Milnes", ("pre-submission", "initiation", "formatting")),
]
if "Author Contributions" not in contrib_blob and "author contributions" not in contrib_blob.lower():
    errors.append("missing Author Contributions block in formalization.yaml / PROVENANCE.md")
for person, hints in required_people:
    if person not in contrib_blob:
        errors.append(f"contributions text missing person token: {person}")
        continue
    if not any(h.lower() in contrib_blob.lower() for h in hints):
        errors.append(f"contributions text missing role hint for {person}: {hints}")

# 2. DomainTheory production disclosure (golf / Comparator packaging)
auto = re.search(r"(?ms)^automation:\n(.*?)(?=^review:\n)", yaml)
auto_text = auto.group(1) if auto else ""
if not re.search(r"(?i)golf", auto_text):
    errors.append("automation must disclose golfed assembly of DomainTheory")
if not re.search(r"(?i)comparator", auto_text):
    errors.append("automation must disclose Comparator packaging")
if "future DomainTheory automation must be appended" in auto_text:
    errors.append("stale automation note: future DomainTheory automation must be appended")

# 3. Review disclosure
review = re.search(r"(?ms)^review:\n(.*?)(?=^known_gaps:\n|^limitations:\n|^alignment:\n)", yaml)
review_text = review.group(1) if review else ""
if "self-assessed" not in review_text and "self-assessed" not in yaml:
    errors.append("review.status / notes must record self-assessed basis")
if not re.search(r"(?i)D.?Silva", review_text):
    errors.append("review.notes must name D'Silva pre-submission advisory review")
if not re.search(r"(?i)Milnes", review_text):
    errors.append("review.notes must name Milnes pre-submission advisory review")
if not re.search(r"(?i)pre-submission", review_text):
    errors.append("review.notes must state pre-submission review basis/extent")

# 4. 1976 scope hygiene
scope_1976 = ""
m1976 = re.search(
    r"\[1976 / scott1976[^\]]*\](.*?)(?=\[1980 / scott1980|\n\n    \[1980)",
    yaml,
    re.S,
)
if m1976:
    scope_1976 = m1976.group(0)
else:
    errors.append("could not locate [1976 / scott1976] scope paragraph")
if re.search(r"1:1 onto", scope_1976):
    errors.append("1976 scope still claims unqualified '1:1 onto' transcription")
root_th = len(cfg["theorem_names"])
root_def = len(cfg["definition_names"])
dtal_th = sum(1 for n in cfg["theorem_names"] if "DataTypesAsLattices" in n)
dtal_def = sum(1 for n in cfg["definition_names"] if "DataTypesAsLattices" in n)
if re.search(rf"\b{root_th}\s+theorem", scope_1976) and not re.search(
    r"(?i)combined|total|bridges", scope_1976
):
    errors.append(
        f"1976 scope assigns combined theorem count {root_th} to the 1976 selection "
        "without distinguishing the combined Comparator"
    )
if re.search(rf"\b{root_def}\s+definition", scope_1976) and not re.search(
    r"(?i)combined|total|bridges", scope_1976
):
    errors.append(
        f"1976 scope assigns combined definition count {root_def} to the 1976 selection "
        "without distinguishing the combined Comparator"
    )
lim = re.search(r"(?ms)^limitations:\n(.*?)(?=^alignment:\n|^sources:\n|\Z)", yaml)
lim_text = lim.group(1) if lim else ""
count_blob = scope_1976 + "\n" + lim_text
if not re.search(rf"\b{root_th}\b", count_blob) or not re.search(rf"\b{root_def}\b", count_blob):
    errors.append(
        f"1976 scope/limitations must state combined Comparator counts "
        f"{root_th} theorems / {root_def} definitions"
    )
if not re.search(rf"\b{dtal_th}\b", count_blob) or not re.search(rf"\b{dtal_def}\b", count_blob):
    errors.append(
        f"1976 scope/limitations must state selected DataTypesAsLattices slice counts "
        f"{dtal_th} theorems / {dtal_def} definitions"
    )

# 5. Compared alignment lean names must resolve to comparator.json
def resolves(lean: str) -> bool:
    for n in cfg["theorem_names"] + cfg["definition_names"]:
        if n == lean or n.endswith("." + lean):
            return True
        parts = n.split(".")
        for i in range(len(parts)):
            if ".".join(parts[i:]) == lean:
                return True
        if n.rsplit(".", 1)[-1] == lean:
            return True
    return False

align = re.search(r"(?ms)^alignment:\n(.*)\Z", yaml)
align_text = align.group(1) if align else ""
stale = []
for m in re.finditer(
    r"(?ms)^    - source:.*?\n      lean: (\S+)\n(?:.*?\n)*?      note: ((?:.|\n)*?)(?=\n    - |\n  - |\n[a-z]|\Z)",
    align_text,
):
    lean, note = m.group(1), m.group(2)
    if "Compared by Palomar" in note and not resolves(lean):
        stale.append(lean)
if stale:
    errors.append(
        "alignment lean names marked 'Compared by Palomar' missing from comparator.json: "
        + ", ".join(sorted(set(stale)))
    )

# 6. Inverse-limit mapping
lean_fields = re.findall(r"(?m)^\s+lean:\s+(\S+)", align_text)
if "theorem_4_6_limit" in lean_fields:
    errors.append("alignment still uses retired lean: theorem_4_6_limit")
retract_ok = False
iso_ok = False
for m in re.finditer(
    r"(?ms)^    - source: (.*?)\n      lean: (\S+)\n(?:.*?\n)*?      note: ((?:.|\n)*?)(?=\n    - |\n  - |\n[a-z]|\Z)",
    align_text,
):
    source, lean, note = m.group(1), m.group(2), m.group(3)
    src_l = source.lower()
    if "4.6" in source and "retract" in src_l:
        if lean == "theorem_4_6.Limit":
            retract_ok = True
        else:
            errors.append(
                f"Theorem 4.6 retracts alignment must use lean: theorem_4_6.Limit (got {lean})"
            )
    if "4.6" in source and (
        "inverse limit" in src_l or "order isomorphism" in src_l or "order-iso" in src_l
    ):
        if lean == "theorem_4_6":
            iso_ok = True
            if not re.search(r"(?i)hstrict|strict", note) or not re.search(
                r"(?i)hmono|monotone|monotonicity", note
            ):
                errors.append(
                    "theorem_4_6 inverse-limit alignment note must state strictness and "
                    "monotonicity hypotheses"
                )
            if not re.search(r"(?i)order iso|≃o|order-iso", note):
                errors.append(
                    "theorem_4_6 inverse-limit alignment note must state order isomorphism"
                )
        else:
            errors.append(
                f"Theorem 4.6 inverse-limit / order-iso alignment must use lean: theorem_4_6 "
                f"(got {lean})"
            )
if not retract_ok:
    errors.append("missing Theorem 4.6 retracts alignment with lean: theorem_4_6.Limit")
if not iso_ok:
    errors.append("missing Theorem 4.6 inverse-limit alignment with lean: theorem_4_6")

# 7. Headline claim notes must be assessable
headline_reqs = {
    "theorem_3_6": (r"(?i)subalgebra|enumeration degree|Deg", "sorry-free"),
    "theorem_6_1": (r"(?i)open|𝔊|Scott-open|0 ∈", "sorry-free"),
    "theorem_6_2": (r"(?i)closed|𝔉|⊥|bot", "sorry-free"),
    "theorem_6_3": (r"(?i)𝔊_δ|Gδ|⊤|top", "sorry-free"),
    "theorem_6_4": (r"(?i)ofNat|𝔉|intersection", "sorry-free"),
    "theorem_6_5": (r"(?i)succSet|specializ", "sorry-free"),
    "theorem_6_6": (r"(?i)Boolean|𝔅|finite", "sorry-free"),
    "theorem_6_7": (r"(?i)equalizer|𝔅_δ|f\(x\) = g\(x\)", "sorry-free"),
    "theorem_7_4": (r"(?i)iterator|Zcomb|η|eta|uniqueness|\(A→A\)", "sorry-free"),
}
notes_by_lean = {}
for m in re.finditer(
    r"(?ms)^    - source:.*?\n      lean: (\S+)\n(?:.*?\n)*?      note: ((?:.|\n)*?)(?=\n    - |\n  - |\n[a-z]|\Z)",
    align_text,
):
    notes_by_lean[m.group(1)] = m.group(2)
for lean, (need, ban) in headline_reqs.items():
    note = notes_by_lean.get(lean)
    if note is None:
        errors.append(f"missing alignment statement for headline {lean}")
        continue
    compact = " ".join(note.split())
    if ban in compact and not re.search(need, compact):
        errors.append(f"{lean} alignment note is title-only / sorry-free without assessable claim")
    elif not re.search(need, compact):
        errors.append(f"{lean} alignment note lacks assessable claim keywords matching {need}")

if errors:
    raise SystemExit("Narrative preflight failed:\n- " + "\n- ".join(errors))
print(
    f"OK: attribution, production/review disclosure, 1976 scope counts "
    f"(combined {root_th}/{root_def}, DTAL {dtal_th}/{dtal_def}), "
    "alignment names, inverse-limit mapping, and headline claims."
)
PY

step "Build Lean project"
lake build

step "Compare Challenge/Solution declaration types"
PALOMAR_QUIET=1 bash scripts/compare_challenge_solution_types.sh

step "Reject proof holes in Solution sources"
if rg -n --glob '*.lean' \
    '(^|:=|by)[[:space:]]+sorry([[:space:];]|$)|^[[:space:]]*sorry([[:space:];]|$)' \
    DomainTheory Solution.lean; then
  echo "FAIL: Solution proof sources contain sorry."
  exit 1
fi
echo "OK: Solution proof sources contain no sorry."

step "Check permitted theorem axioms"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
python3 - "$tmp/Axioms.lean" <<'PY'
import json
import sys

with open("comparator.json", encoding="utf-8") as f:
    cfg = json.load(f)
with open(sys.argv[1], "w", encoding="utf-8") as out:
    out.write(f"import {cfg['solution_module']}\n")
    for name in cfg["theorem_names"]:
        out.write(f"#print axioms {name}\n")
PY
lake env lean "$tmp/Axioms.lean" >"$tmp/axioms.txt"
python3 - "$tmp/axioms.txt" <<'PY'
import json
import re
import sys

with open("comparator.json", encoding="utf-8") as f:
    cfg = json.load(f)
allowed = set(cfg["permitted_axioms"])
text = open(sys.argv[1], encoding="utf-8").read()
reports = re.findall(
    r"^'(.+)' depends on axioms: \[([^\]]*)\]$", text, re.MULTILINE
)
axiom_free = re.findall(
    r"^'(.+)' does not depend on any axioms$", text, re.MULTILINE
)
reported = {name for name, _ in reports} | set(axiom_free)
expected = set(cfg["theorem_names"])
if reported != expected:
    missing = sorted(expected - reported)
    extra = sorted(reported - expected)
    raise SystemExit(f"Axiom report mismatch; missing={missing}, extra={extra}")
for name, raw in reports:
    used = {item.strip() for item in raw.split(",") if item.strip()}
    forbidden = sorted(used - allowed)
    if forbidden:
        raise SystemExit(f"{name} uses forbidden axioms: {', '.join(forbidden)}")
print(f"OK: all theorem targets use only {sorted(allowed)}.")
PY

step "Check patch formatting"
git diff --check
echo "OK: Palomar preflight passed."
