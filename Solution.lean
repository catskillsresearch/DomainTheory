module
/-
Copyright (c) 2026 DomainTheory authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Dana Scott, Vijay d'Silva, Brian Milnes

Author Contributions:
* Lars Warren Ericson: Primary formalization engineer. Responsible for all
  Lean 4 code, AI-assisted proof architecture, and repository assembly.
* Dana S. Scott: Author of the original source mathematics (1972–1982).
  Provided project sponsorship, historical context, and high-level advisory
  oversight of the formalization scope.
* Vijay D'Silva & Brian Milnes: Provided project initiation, pre-submission
  review, and advisory feedback on repository formatting and technical
  report generation.
-/
public import DomainTheory

/-!
# Solutions to the Challenge

Imports the DomainTheory library (golfed assembly of the five vendored
formalizations). Comparator matches the compared declarations named in
`Challenge.lean` / `comparator.json` against these proved definitions and
theorems. There is no `sorry` in the DomainTheory proof modules.
-/
