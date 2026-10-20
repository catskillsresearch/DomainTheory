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
public import DomainTheory.Neighborhood.Proposition810.toElementMap_le_of_comp_le_idMap
public import DomainTheory.Neighborhood.Proposition810.toElementMap_le_self_of_le_idMap
public import DomainTheory.Neighborhood.Proposition810.toElementMap_sumComb_of_left
public import DomainTheory.Neighborhood.Proposition810.toElementMap_sumComb_of_right
public import DomainTheory.Neighborhood.Proposition810.toElementMap_sumComb_of_neither

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}




/-- **Proposition 8.10, `+`-case, projection half.** -/
theorem le_idMap_sumComb {a b : ApproximableMap U U} (ha : a ≤ idMap U) (hb : b ≤ idMap U) :
    sumComb a b ≤ idMap U := by
  rw [le_iff_toElementMap_le]
  intro x
  rw [toElementMap_idMap]
  rcases sum_element_trichotomy (jPlus.toElementMap x) with hL | hR | hN
  · calc (sumComb a b).toElementMap x
        = iPlus.toElementMap ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            (a.toElementMap ((outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
              (jPlus.toElementMap x)))) := toElementMap_sumComb_of_left hL
      _ ≤ iPlus.toElementMap ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            ((outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
              (jPlus.toElementMap x))) :=
          iPlus.toElementMap_mono (inMap₀.toElementMap_mono (toElementMap_le_self_of_le_idMap ha _))
      _ = iPlus.toElementMap (jPlus.toElementMap x) := by rw [inMap₀_outMap₀_eq_of_left hL]
      _ ≤ x := toElementMap_le_of_comp_le_idMap iPlus_comp_jPlus_le x
  · calc (sumComb a b).toElementMap x
        = iPlus.toElementMap ((inMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            (b.toElementMap ((outMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
              (jPlus.toElementMap x)))) := toElementMap_sumComb_of_right hR
      _ ≤ iPlus.toElementMap ((inMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            ((outMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
              (jPlus.toElementMap x))) :=
          iPlus.toElementMap_mono (inMap₁.toElementMap_mono (toElementMap_le_self_of_le_idMap hb _))
      _ = iPlus.toElementMap (jPlus.toElementMap x) := by rw [inMap₁_outMap₁_eq_of_right hR]
      _ ≤ x := toElementMap_le_of_comp_le_idMap iPlus_comp_jPlus_le x
  · rw [toElementMap_sumComb_of_neither hN]
    exact U.bot_le x

end DomainTheory.Neighborhood
