/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Topology.Inseparable
import DomainTheory.Neighborhood.Exercise122.Basic
import DomainTheory.Neighborhood.Exercise122.le_iff_isOpen_imp


namespace DomainTheory.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)







/-- The approximation order `⊑` is the opposite of Mathlib's specialization preorder `⤳`:
`y ⤳ x ↔ x ⊑ y`. (Scott's (iii) says exactly that `⊑` is the specialization order of this
topology.) -/
theorem specializes_iff_le (x y : V.Element) : y ⤳ x ↔ x ≤ y := by
  rw [specializes_iff_forall_open]
  exact (V.le_iff_isOpen_imp x y).symm

end NeighborhoodSystem
end DomainTheory.Neighborhood
