/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example23
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Example43.Basic
import DomainTheory.Neighborhood.Example43.mem_natElem_iff


namespace DomainTheory.Neighborhood.Example43

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap

















/-- **Computation on the total elements.** `f(n̂) = val n`. -/
theorem constLiftN_natElem {β : Type*} (V : NeighborhoodSystem β) (val : ℕ → V.Element) (n : ℕ) :
    (constLiftN V val).toElementMap (natElem n) = val n := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hXmem, hrel⟩
    rw [mem_natElem_iff] at hXmem
    rcases hrel with ⟨_, rfl⟩ | ⟨k, hXk, hY⟩
    · exact (val n).master_mem
    · rcases hXmem with rfl | rfl
      · exact (univ_ne_singleton k hXk).elim
      · have hnk : n = k := singleton_nat_inj hXk
        subst hnk; exact hY
  · intro hY
    exact ⟨{n}, mem_natElem_iff.mpr (Or.inr rfl), Or.inr ⟨n, rfl, hY⟩⟩

end DomainTheory.Neighborhood.Example43
