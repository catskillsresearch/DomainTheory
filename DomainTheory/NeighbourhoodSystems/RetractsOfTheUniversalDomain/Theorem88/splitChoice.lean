/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import Mathlib.Data.Fintype.Pi
import all Mathlib.Data.Fintype.Pi
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.exists_split

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

open Classical in
/-- **Total packaging of `exists_split`.** Given any `A : Set α`, `B : Set ℚ`, `Xn : Set α`,
`splitChoice A B Xn` is the pair `(I, J)` produced by `exists_split` whenever the hypotheses hold
(`A = ∅ ↔ B = ∅` and `B = ∅ ∨ U.mem B`), and the junk value `(∅, ∅)` otherwise. Making this total
(rather than threading proof obligations through a dependent recursive definition) is what lets
`atomU` below be defined by plain structural recursion on `ℕ`; `splitChoice_isSplitSpec` recovers
`exists_split`'s conclusions whenever the hypotheses genuinely hold, which is all that is ever
used (the junk branch is never reached along the real construction). -/
noncomputable def splitChoice (A : Set α) (B : Set ℚ) (Xn : Set α) : Set ℚ × Set ℚ :=
  if h : (A = ∅ ↔ B = ∅) ∧ (B = ∅ ∨ U.mem B) then
    ⟨(exists_split h.1 h.2 Xn).choose, (exists_split h.1 h.2 Xn).choose_spec.choose⟩
  else (∅, ∅)

end DomainTheory.NeighbourhoodSystems
