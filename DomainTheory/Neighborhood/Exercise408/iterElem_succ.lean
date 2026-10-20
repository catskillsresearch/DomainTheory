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


/-- `fⁿ⁺¹(⊥) = f(fⁿ(⊥))`. -/
theorem iterElem_succ (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem (n + 1) = f.toElementMap (f.iterElem n) := by
  show (f.comp (f.iterMap n)).toElementMap V.bot
      = f.toElementMap ((f.iterMap n).toElementMap V.bot)
  rw [toElementMap_comp]

end ApproximableMap
end DomainTheory.Neighborhood
