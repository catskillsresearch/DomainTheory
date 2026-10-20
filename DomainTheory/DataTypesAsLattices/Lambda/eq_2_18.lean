/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.eq_2_18_bot
import DomainTheory.DataTypesAsLattices.Lambda.eq_2_18_top
import DomainTheory.DataTypesAsLattices.Lambda.pair_eq_right
import DomainTheory.DataTypesAsLattices.Lambda.exists_least_not_mem
import DomainTheory.DataTypesAsLattices.Lambda.exists_least_mem


namespace DomainTheory.DataTypesAsLattices





































/-- **Scott 1976, (2.18).** `a = λx. a` iff `a = ⊥` or `a = ⊤`. -/
theorem eq_2_18 (a : Pomega) :
    a = graph (fun _ => a) ↔ a = botElem ∨ a = topElem := by
  constructor
  · intro ha
    by_cases htop : a = topElem
    · exact Or.inr htop
    · have hex : ∃ k, k ∉ a := by
        by_contra h
        apply htop
        ext k
        constructor
        · intro; trivial
        · intro
          exact not_not.mp (not_exists.mp h k)
      obtain ⟨k, hk, hmin⟩ := exists_least_not_mem hex
      obtain ⟨n, m, hnm⟩ := exists_pair k
      have hm : m ∉ a := by
        intro hma
        have : pair n m ∈ a :=
          ha.symm ▸ (⟨n, m, rfl, hma⟩ : pair n m ∈ graph (fun _ => a))
        exact hk (by rwa [hnm] at this)
      have : m = k :=
        le_antisymm (by rw [← hnm]; exact pair_le_right n m)
          (le_of_not_gt fun hlt => hm (hmin m hlt))
      have hnmk : pair n k = k := by simpa [this] using hnm
      have ⟨_, hk0⟩ := pair_eq_right hnmk
      have h0 : 0 ∉ a := by simpa [hk0] using hk
      by_cases hbot : a = botElem
      · exact Or.inl hbot
      · obtain ⟨l, hl, hlmin⟩ := exists_least_mem (Set.nonempty_iff_ne_empty.mpr hbot)
        obtain ⟨i, j, hij⟩ := exists_pair l
        have hj : j ∈ a := by
          have : pair i j ∈ graph (fun _ => a) :=
            ha ▸ (by rwa [hij] : pair i j ∈ a)
          rcases this with ⟨i', j', hp, hj'⟩
          obtain ⟨rfl, rfl⟩ := pair_inj hp
          exact hj'
        have : j = l :=
          le_antisymm (by rw [← hij]; exact pair_le_right i j)
            (le_of_not_gt fun hlt => hlmin j hlt hj)
        have hil : pair i l = l := by simpa [this] using hij
        have ⟨_, hl0⟩ := pair_eq_right hil
        exact (h0 (by simpa [hl0] using hl)).elim
  · intro h
    rcases h with rfl | rfl
    · exact eq_2_18_bot
    · exact eq_2_18_top

end DomainTheory.DataTypesAsLattices
