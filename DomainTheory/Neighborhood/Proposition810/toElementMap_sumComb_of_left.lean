/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition89
import DomainTheory.Neighborhood.Definition83
import DomainTheory.Neighborhood.Theorem69
import DomainTheory.Neighborhood.Proposition810.Basic
import DomainTheory.Neighborhood.Proposition810.not_sum_reaches_both
import DomainTheory.Neighborhood.Proposition810.toElementMap_sumComb_mem


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}




/-- **On a "left" point** (`jPlus x` reaches the left copy), `sumComb a b` evaluates to Scott's
literal `i₊∘in₀∘a∘out₀` formula. -/
theorem toElementMap_sumComb_of_left {a b : ApproximableMap U U} {x : U.Element}
    (hL : ∃ X, U.mem X ∧ (jPlus.toElementMap x).mem (inj₀ X)) :
    (sumComb a b).toElementMap x =
      iPlus.toElementMap ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
        (a.toElementMap ((outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
          (jPlus.toElementMap x)))) := by
  have hz : ((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap
      (jPlus.toElementMap x)).mem Example12.zero := which_mem_zero.mpr hL
  have hno : ¬ ((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap
      (jPlus.toElementMap x)).mem Example12.one :=
    fun h => not_sum_reaches_both hL (which_mem_one.mp h)
  apply Element.ext
  intro Z
  rw [toElementMap_sumComb_mem]
  constructor
  · rintro (⟨_, h⟩ | ⟨h1, _⟩ | rfl)
    · exact h
    · exact absurd h1 hno
    · exact Element.master_mem _
  · intro h
    exact Or.inl ⟨hz, h⟩

end DomainTheory.Neighborhood
