/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Exercise326
import DomainTheory.Neighborhood.Exercise512.Basic
import DomainTheory.Neighborhood.Exercise512.whileMap_rec


namespace DomainTheory.Neighborhood.Exercise512

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Exercise326 (cond TD)

variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)





/-- If the test fails (`p(x) = false`), the loop exits: `w(x) = x`. -/
theorem whileMap_false {x : V.Element} (hx : p.toElementMap x = Example23.falseElt) :
    (whileMap V p f).toElementMap x = x := by
  rw [whileMap_rec, hx, Exercise326.cond_false]

end DomainTheory.Neighborhood.Exercise512
