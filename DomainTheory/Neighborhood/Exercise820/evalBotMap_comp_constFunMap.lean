/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise817
import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise820.Basic
import DomainTheory.Neighborhood.Exercise820.toElementMap_evalBotMap


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u v




section FunSpace

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)




theorem evalBotMap_comp_constFunMap : (evalBotMap A B).comp (constFunMap A B) = idMap B := by
  apply le_antisymm <;> rw [le_iff_toElementMap_le] <;> intro b <;>
    rw [toElementMap_comp, toElementMap_idMap, toElementMap_evalBotMap, toApproxMap_constFunMap]

end FunSpace
end DomainTheory.Neighborhood
