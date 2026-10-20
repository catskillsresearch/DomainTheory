/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Data.Finset.Basic
import DomainTheory.DataTypesAsLattices.FixedLattices.Basic


namespace DomainTheory.DataTypesAsLattices










theorem finiteBasisSups_directed {α : Type u} [CompleteLattice α]
    (d : ℕ → α) (x : Set ℕ) :
    IsDirectedSet (finiteBasisSups d x) := by
  constructor
  · exact ⟨sSup (d '' ((∅ : Finset ℕ) : Set ℕ)), ∅, by simp, rfl⟩
  · rintro y ⟨t, htx, rfl⟩ z ⟨u, hux, rfl⟩
    refine ⟨sSup (d '' ((t ∪ u : Finset ℕ) : Set ℕ)),
      ⟨t ∪ u, ?_, rfl⟩, ?_, ?_⟩
    · intro n hn
      simp only [Finset.coe_union, Set.mem_union] at hn
      exact hn.elim (fun h => htx h) (fun h => hux h)
    · apply sSup_le
      intro q hq
      apply le_sSup
      exact Set.image_mono (by
        intro n hn
        exact by simp [hn]) hq
    · apply sSup_le
      intro q hq
      apply le_sSup
      exact Set.image_mono (by
        intro n hn
        exact by simp [hn]) hq

end DomainTheory.DataTypesAsLattices
