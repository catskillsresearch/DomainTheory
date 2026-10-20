/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Exercise326
import DomainTheory.Neighborhood.Exercise512.Basic
import DomainTheory.Neighborhood.Exercise512.Wop_apply


namespace DomainTheory.Neighborhood.Exercise512

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Exercise326 (cond TD)

variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)





/-- **Exercise 5.12 (Scott 1981, PRG-19).** The defining recursion of the `while`-loop:
`w(x) = cond(p(x), w(f(x)), x)`. -/
theorem whileMap_rec (x : V.Element) :
    (whileMap V p f).toElementMap x =
      (cond V).toElementMap
        (pair (p.toElementMap x)
          (pair ((whileMap V p f).toElementMap (f.toElementMap x)) x)) := by
  have hfix : (Wop V p f).toElementMap (whileFix V p f) = whileFix V p f :=
    toElementMap_fixElement (Wop V p f)
  have := Wop_apply V p f (whileFix V p f) x
  rw [hfix] at this
  exact this

end DomainTheory.Neighborhood.Exercise512
