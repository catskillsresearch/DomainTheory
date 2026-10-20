/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Product
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import DomainTheory.Neighborhood.Exercise629.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}







variable {D : ∀ i, NeighborhoodSystem (α i)}












theorem injI_inter_ne {i j : ι} (h : i ≠ j) (X : Set (α i)) (Y : Set (α j)) :
    injI i X ∩ injI j Y = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro (_ | ⟨k, a⟩) ⟨hw1, hw2⟩
  · exact none_not_mem_injI hw1
  · exact h ((index_of_some_mem_injI hw1).symm.trans (index_of_some_mem_injI hw2))

end Exercise629
end DomainTheory.Neighborhood
