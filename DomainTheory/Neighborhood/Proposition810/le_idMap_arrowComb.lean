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
import DomainTheory.Neighborhood.Proposition810.toElementMap_le_of_comp_le_idMap
import DomainTheory.Neighborhood.Proposition810.toElementMap_le_self_of_le_idMap
import DomainTheory.Neighborhood.Proposition810.le_idMap_lamComb
import DomainTheory.Neighborhood.Proposition810.toElementMap_arrowComb


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}



/-- **Proposition 8.10, `→`-case, projection half.** -/
theorem le_idMap_arrowComb {a b : ApproximableMap U U} (ha : a ≤ idMap U) (hb : b ≤ idMap U) :
    arrowComb a b ≤ idMap U := by
  rw [le_iff_toElementMap_le]
  intro x
  rw [toElementMap_arrowComb, toElementMap_idMap]
  calc iArrow.toElementMap ((lamComb a b).toElementMap (jArrow.toElementMap x))
      ≤ iArrow.toElementMap (jArrow.toElementMap x) :=
        iArrow.toElementMap_mono
          (toElementMap_le_self_of_le_idMap (le_idMap_lamComb ha hb) _)
    _ ≤ x := toElementMap_le_of_comp_le_idMap iArrow_comp_jArrow_le x

end DomainTheory.Neighborhood
