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
import DomainTheory.Neighborhood.Proposition810.toElementMap_of_comp_eq_idMap
import DomainTheory.Neighborhood.Proposition810.toElementMap_idem_of_isRetraction
import DomainTheory.Neighborhood.Proposition810.inMapu2080_toElementMap_reaches_left
import DomainTheory.Neighborhood.Proposition810.inMapu2081_toElementMap_reaches_right
import DomainTheory.Neighborhood.Proposition810.jPlus_bot_eq_bot
import DomainTheory.Neighborhood.Proposition810.toElementMap_sumComb_of_left
import DomainTheory.Neighborhood.Proposition810.toElementMap_sumComb_of_right
import DomainTheory.Neighborhood.Proposition810.toElementMap_sumComb_of_neither


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}




/-- **Proposition 8.10, `+`-case, retraction half.** -/
theorem isRetraction_sumComb {a b : ApproximableMap U U} (ha : IsRetraction a)
    (hb : IsRetraction b) : IsRetraction (sumComb a b) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp]
  rcases sum_element_trichotomy (jPlus.toElementMap x) with hL | hR | hN
  · rw [toElementMap_sumComb_of_left hL]
    set v := a.toElementMap (outMap₀.toElementMap (jPlus.toElementMap x)) with hv
    have hjy : jPlus.toElementMap (iPlus.toElementMap (inMap₀.toElementMap v))
        = inMap₀.toElementMap v := toElementMap_of_comp_eq_idMap jPlus_comp_iPlus _
    have hLy : ∃ X, U.mem X ∧
        (jPlus.toElementMap (iPlus.toElementMap (inMap₀.toElementMap v))).mem (inj₀ X) := by
      rw [hjy]; exact inMap₀_toElementMap_reaches_left v
    rw [toElementMap_sumComb_of_left hLy, hjy,
      toElementMap_of_comp_eq_idMap outMap₀_comp_inMap₀ v, toElementMap_idem_of_isRetraction ha]
  · rw [toElementMap_sumComb_of_right hR]
    set v := b.toElementMap (outMap₁.toElementMap (jPlus.toElementMap x)) with hv
    have hjy : jPlus.toElementMap (iPlus.toElementMap (inMap₁.toElementMap v))
        = inMap₁.toElementMap v := toElementMap_of_comp_eq_idMap jPlus_comp_iPlus _
    have hRy : ∃ Y, U.mem Y ∧
        (jPlus.toElementMap (iPlus.toElementMap (inMap₁.toElementMap v))).mem (inj₁ Y) := by
      rw [hjy]; exact inMap₁_toElementMap_reaches_right v
    rw [toElementMap_sumComb_of_right hRy, hjy,
      toElementMap_of_comp_eq_idMap outMap₁_comp_inMap₁ v, toElementMap_idem_of_isRetraction hb]
  · rw [toElementMap_sumComb_of_neither hN]
    apply toElementMap_sumComb_of_neither
    intro W hW
    rw [jPlus_bot_eq_bot, mem_bot] at hW
    exact hW

end DomainTheory.Neighborhood
