/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise316
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Exercise511.Basic
import DomainTheory.Neighborhood.Exercise511.unfold_fold


namespace DomainTheory.Neighborhood.Exercise511

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)











/-- **Stack law.** `tail(push(x, s)) = s`. -/
theorem tail_push (x : V.Element) (s : (iterSys V).Element) :
    (tail V).toElementMap ((push V).toElementMap (pair x s)) = s := by
  rw [tail, toElementMap_comp, push, unfold_fold, toElementMap_proj₁, snd_pair]

end DomainTheory.Neighborhood.Exercise511
