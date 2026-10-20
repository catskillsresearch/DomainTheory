/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem41
public import DomainTheory.Neighborhood.Exercise326
public import DomainTheory.Neighborhood.Exercise512.Basic
public import DomainTheory.Neighborhood.Exercise512.whileMap_rec

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise512

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Exercise326 (cond TD)

variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)





/-- If the test diverges (`p(x) = ⊥`), the loop diverges: `w(x) = ⊥`. -/
theorem whileMap_bot {x : V.Element} (hx : p.toElementMap x = Example23.botElt) :
    (whileMap V p f).toElementMap x = V.bot := by
  rw [whileMap_rec, hx, Exercise326.cond_bot]

end DomainTheory.Neighborhood.Exercise512
