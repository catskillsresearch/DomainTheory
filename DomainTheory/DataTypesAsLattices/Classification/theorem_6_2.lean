/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import Mathlib.Data.Set.Finite.Powerset
import DomainTheory.DataTypesAsLattices.Classification.Basic


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace






















/-- **Scott 1976, Theorem 6.2 (The 𝔉 theorem).** -/
theorem theorem_6_2 :
    ∀ U, U ∈ ScottF ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x = botElem} := by
  intro U
  constructor
  · intro hU
    refine ⟨charTop Uᶜ, charTop_isScottContinuous Uᶜ, ?_⟩
    ext x
    exact (charTop_eq_bot_of_closed hU x).symm
  · rintro ⟨f, hf, rfl⟩
    change IsScottOpen {x | f x = botElem}ᶜ
    have : {x | f x = botElem}ᶜ = ⋃ k, {x | k ∈ f x} := by
      ext x
      constructor
      · intro hx
        have hx' : f x ≠ botElem := hx
        have : ∃ k, k ∈ f x := by
          by_contra hnone
          apply hx'
          ext n
          constructor
          · intro hn
            exact (hnone ⟨n, hn⟩).elim
          · intro hn
            exact ((mem_botElem n).mp hn).elim
        exact Set.mem_iUnion.mpr this
      · intro hx hbot
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
        have hk' : k ∈ f x := hk
        have hbot' : f x = botElem := hbot
        rw [hbot'] at hk'
        exact ((mem_botElem k).mp hk').elim
    rw [this]
    exact isScottOpen_iUnion _ fun k => mem_preimage_isScottOpen hf k

end DomainTheory.DataTypesAsLattices
