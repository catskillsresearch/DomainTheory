/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Theorem41.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap
















/-- `fⁿ(⊥)` agrees with the iterated elementwise function `(f(·))^[n] ⊥` — Scott's `fⁿ(⊥)`. -/
theorem iterElem_eq_iterate (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem n = (f.toElementMap)^[n] V.bot := by
  induction n with
  | zero =>
    show (f.iterMap 0).toElementMap V.bot = V.bot
    exact toElementMap_idMap V.bot
  | succ k ih =>
    have hstep : f.iterElem (k + 1) = f.toElementMap (f.iterElem k) := by
      show (f.comp (f.iterMap k)).toElementMap V.bot
          = f.toElementMap ((f.iterMap k).toElementMap V.bot)
      rw [toElementMap_comp]
    rw [hstep, ih, Function.iterate_succ', Function.comp_apply]

end ApproximableMap
end DomainTheory.Neighborhood
