/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Exercise408.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


theorem mem_supChain (s : ℕ → V.Element) (hmono : Monotone s) {Z : Set α} :
    (supChain s hmono).mem Z ↔ ∃ n, (s n).mem Z :=
  NeighborhoodSystem.mem_iSupDirected s _

end ApproximableMap
end DomainTheory.Neighborhood
