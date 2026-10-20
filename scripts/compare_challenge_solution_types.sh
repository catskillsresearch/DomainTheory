#!/usr/bin/env bash
# Diff Challenge vs Solution declaration types for every comparator.json name.
# Palomar Comparator compares exported types, including exact universe parameter
# names and instance paths. A green `lake build` does not imply a match.
#
# DomainTheory version: the compared names are read from this repo's
# comparator.json (theorem_names + definition_names) instead of a hard-coded
# list inherited from scott_models. Author comparator.json for DomainTheory
# before running this.
set -euo pipefail
cd "$(dirname "$0")/.."

mapfile -t NAMES < <(python3 - <<'PY'
import json

with open("comparator.json", encoding="utf-8") as f:
    cfg = json.load(f)
for name in cfg["theorem_names"] + cfg["definition_names"]:
    print(name)
PY
)

if [[ "${#NAMES[@]}" -eq 0 ]]; then
  echo "FAIL: comparator.json lists no theorem/definition names to compare." >&2
  exit 1
fi

# Comparator also walks constructors of structures used in those types.
# Add DomainTheory structure names (and their .mk / nested structures) here
# as the library grows, e.g.:
#   DomainTheory.SomeStructure
#   DomainTheory.SomeStructure.mk
EXTRA_PRINTS=(
)

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

write_lean() {
  local module="$1" out="$2"
  {
    echo "import ${module}"
    echo "set_option pp.all true"
    echo "set_option pp.explicit true"
    echo "set_option pp.universes true"
    echo "set_option pp.funBinderTypes true"
    for n in "${NAMES[@]}"; do
      echo "#check ${n}"
    done
    for n in "${EXTRA_PRINTS[@]}"; do
      echo "#print ${n}"
    done
  } >"${out}"
}

write_lean Challenge "${tmp}/ChallengeTypes.lean"
write_lean Solution "${tmp}/SolutionTypes.lean"

lake env lean "${tmp}/ChallengeTypes.lean" 2>/dev/null \
  | grep -vE 'LEAN_PATH|trace:|warning:|declaration uses' \
  >"${tmp}/challenge.txt" || true
lake env lean "${tmp}/SolutionTypes.lean" 2>/dev/null \
  | grep -vE 'LEAN_PATH|trace:|warning:|declaration uses' \
  >"${tmp}/solution.txt" || true

echo "== Challenge (pp.all, exact universe names) =="
cat "${tmp}/challenge.txt"
echo
echo "== Solution (pp.all, exact universe names) =="
cat "${tmp}/solution.txt"
echo
if diff -u "${tmp}/challenge.txt" "${tmp}/solution.txt"; then
  echo "OK: Challenge and Solution types match exactly."
else
  echo "FAIL: type/universe/instance mismatch — Palomar Comparator will reject this."
  exit 1
fi
