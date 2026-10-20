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



theorem proj₁_comp_embedSnd : (proj₁ A B).comp (embedSnd A B) = idMap B := by
  apply le_antisymm <;> rw [le_iff_toElementMap_le] <;> intro b <;>
    simp [embedSnd, toElementMap_comp, toElementMap_idMap, toElementMap_paired, toElementMap_constMap,
      toElementMap_proj₁, snd_pair]

end Prod
end DomainTheory.Neighborhood
