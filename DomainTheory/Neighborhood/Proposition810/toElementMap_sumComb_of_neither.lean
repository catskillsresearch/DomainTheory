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
public import DomainTheory.Neighborhood.Proposition810.toElementMap_sumComb_mem

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}




/-- **On a point reaching neither copy** (in particular, `𝒰`'s own `⊥`, via `jPlus_bot_eq_bot`),
`sumComb a b` sends it to `𝒰`'s `⊥`. -/
theorem toElementMap_sumComb_of_neither {a b : ApproximableMap U U} {x : U.Element}
    (hN : ∀ W, (jPlus.toElementMap x).mem W → W = (sum U U U_mem_nonempty U_mem_nonempty).master) :
    (sumComb a b).toElementMap x = U.bot := by
  have hnz : ¬ ((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap
      (jPlus.toElementMap x)).mem Example12.zero := by
    rw [which_mem_zero]
    rintro ⟨X, _, hX⟩
    exact inj₀_ne_sumMaster (hN _ hX)
  have hno : ¬ ((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap
      (jPlus.toElementMap x)).mem Example12.one := by
    rw [which_mem_one]
    rintro ⟨Y, _, hY⟩
    exact inj₁_ne_sumMaster (hN _ hY)
  apply Element.ext
  intro Z
  rw [toElementMap_sumComb_mem, mem_bot]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | h)
    · exact absurd h hnz
    · exact absurd h hno
    · exact h
  · intro h
    exact Or.inr (Or.inr h)

end DomainTheory.Neighborhood
