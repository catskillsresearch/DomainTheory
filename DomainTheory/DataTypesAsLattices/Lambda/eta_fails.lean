/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.e_one

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





























/-- **Scott 1976, Table 1 (η) fails.** Not every element is a graph. -/
theorem eta_fails : ∃ u, graph (funOf u) ≠ u := by
  refine ⟨{pair 1 0}, ?_⟩
  intro h
  have hG : IsGraph {pair 1 0} := (theorem_1_2_iii _).mp h
  have hsub : e 1 ⊆ e 3 := by
    intro k hk
    have : k = 0 := by
      simpa [e_one] using hk
    subst this
    decide
  have : pair 3 0 ∈ ({pair 1 0} : Pomega) :=
    hG (by simp) hsub
  have : pair 3 0 = pair 1 0 := this
  exact (by simp [pair] : pair 3 0 ≠ pair 1 0) this

end DomainTheory.DataTypesAsLattices
