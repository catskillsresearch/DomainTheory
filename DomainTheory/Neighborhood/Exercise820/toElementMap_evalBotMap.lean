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




section FunSpace

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)




theorem toElementMap_evalBotMap (φ : (funSpace A B).Element) :
    (evalBotMap A B).toElementMap φ = (toApproxMap φ).toElementMap A.bot := by
  simp [evalBotMap, toElementMap_comp, toElementMap_paired, toElementMap_idMap,
    toElementMap_constMap, evalMap_apply]

end FunSpace
end DomainTheory.Neighborhood
