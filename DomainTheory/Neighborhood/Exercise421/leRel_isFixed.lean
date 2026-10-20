/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.Neighborhood.Exercise421.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise421

open DomainTheory.Neighborhood.Exercise414




/-- **Exercise 4.21 (Scott 1981, PRG-19).** `≤` solves Scott's fixed-point equation. -/
theorem leRel_isFixed : leOp leRel = leRel := by
  apply Set.Subset.antisymm
  · rintro ⟨n, m⟩ (h | ⟨k, hk, rfl⟩)
    · exact le_of_eq (h : n = m)
    · exact Nat.le_succ_of_le (hk : n ≤ k)
  · rintro ⟨n, m⟩ (h : n ≤ m)
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · exact Or.inl h'
    · refine Or.inr ⟨m - 1, ?_, ?_⟩
      · change n ≤ m - 1; omega
      · omega

end DomainTheory.Neighborhood.Exercise421
