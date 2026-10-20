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










theorem sSup_finiteBasisSups {α : Type u} [CompleteLattice α]
    (d : ℕ → α) (x : Set ℕ) :
    sSup (finiteBasisSups d x) = sSup (d '' x) := by
  apply le_antisymm
  · apply sSup_le
    rintro y ⟨t, htx, rfl⟩
    apply sSup_le
    intro q hq
    exact le_sSup (Set.image_mono htx hq)
  · apply sSup_le
    rintro _ ⟨n, hn, rfl⟩
    calc
      d n ≤ sSup (d '' (({n} : Finset ℕ) : Set ℕ)) :=
        le_sSup ⟨n, by simp, rfl⟩
      _ ≤ sSup (finiteBasisSups d x) :=
        le_sSup ⟨{n}, by simpa, rfl⟩

end DomainTheory.DataTypesAsLattices
