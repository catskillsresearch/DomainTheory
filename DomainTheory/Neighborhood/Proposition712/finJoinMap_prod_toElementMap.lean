/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition711
import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Proposition710
import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Lemma615
import Mathlib.Tactic
import DomainTheory.Neighborhood.Proposition712.Basic
import DomainTheory.Neighborhood.Proposition712.PDfinJoinApproxMapu2082_toElementMap


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)











theorem finJoinMap_prod_toElementMap (x y : V.Element) :
    (finJoinMap_prod (V := V)).toElementMap (pair x y) = V.PDfinJoin 2 ![x, y] := by
  have hmap : toMap₂ (finJoinMap_prod (V := V)) = PDfinJoinApproxMap₂ (V := V) := toMap₂_ofMap₂ _
  rw [← toElementMap₂_toMap₂ (finJoinMap_prod (V := V)), hmap, PDfinJoinApproxMap₂_toElementMap]

end NeighborhoodSystem
end DomainTheory.Neighborhood
