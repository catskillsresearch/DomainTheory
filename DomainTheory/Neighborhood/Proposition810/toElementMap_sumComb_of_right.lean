/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition89
public import DomainTheory.Neighborhood.Definition83
public import DomainTheory.Neighborhood.Theorem69
public import DomainTheory.Neighborhood.Proposition810.Basic
public import DomainTheory.Neighborhood.Proposition810.not_sum_reaches_both
public import DomainTheory.Neighborhood.Proposition810.toElementMap_sumComb_mem

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}




/-- **On a "right" point**, symmetric to `toElementMap_sumComb_of_left`. -/
theorem toElementMap_sumComb_of_right {a b : ApproximableMap U U} {x : U.Element}
    (hR : ∃ Y, U.mem Y ∧ (jPlus.toElementMap x).mem (inj₁ Y)) :
    (sumComb a b).toElementMap x =
      iPlus.toElementMap ((inMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
        (b.toElementMap ((outMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
          (jPlus.toElementMap x)))) := by
  have ho : ((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap
      (jPlus.toElementMap x)).mem Example12.one := which_mem_one.mpr hR
  have hnz : ¬ ((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap
      (jPlus.toElementMap x)).mem Example12.zero :=
    fun h => not_sum_reaches_both (which_mem_zero.mp h) hR
  apply Element.ext
  intro Z
  rw [toElementMap_sumComb_mem]
  constructor
  · rintro (⟨h1, _⟩ | ⟨_, h⟩ | rfl)
    · exact absurd h1 hnz
    · exact h
    · exact Element.master_mem _
  · intro h
    exact Or.inr (Or.inl ⟨ho, h⟩)

end DomainTheory.Neighborhood
