/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise817
import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise820.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u v


section Prod

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)



theorem proj₀_comp_embedFst : (proj₀ A B).comp (embedFst A B) = idMap A := by
  apply le_antisymm <;> rw [le_iff_toElementMap_le] <;> intro a <;>
    simp [embedFst, toElementMap_comp, toElementMap_idMap, toElementMap_paired, toElementMap_constMap,
      toElementMap_proj₀, fst_pair]

end Prod
end DomainTheory.Neighborhood
