/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Graph
import DomainTheory.DataTypesAsLattices.FixedPoint.Basic


namespace DomainTheory.DataTypesAsLattices

theorem chain_mono (xs : ℕ → Pomega) (hmono : ∀ n, xs n ⊆ xs (n + 1)) :
    ∀ a b, a ≤ b → xs a ⊆ xs b := by
  intro a b hab
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hab
  subst hd
  clear hab
  induction d with
  | zero => simp
  | succ d ih => exact subset_trans ih (hmono _)

end DomainTheory.DataTypesAsLattices
