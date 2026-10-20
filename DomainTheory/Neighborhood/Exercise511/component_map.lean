/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise316
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Exercise511.Basic
import DomainTheory.Neighborhood.Exercise511.component_tail
import DomainTheory.Neighborhood.Exercise511.head_push
import DomainTheory.Neighborhood.Exercise511.tail_push
import DomainTheory.Neighborhood.Exercise511.map_rec


namespace DomainTheory.Neighborhood.Exercise511

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)


















/-- **Exercise 5.11 (Scott 1981, PRG-19).** The `n`-th component of `map(s, x)` is `(component s n)(x)`,
i.e. `map(⟨fₙ⟩, x) = ⟨fₙ(x)⟩ₙ`. -/
theorem component_map (x : V.Element) :
    ∀ (n : ℕ) (s : (iterSys (funSpace V V)).Element),
      component ((mapMap V).toElementMap (pair s x)) n =
        (toApproxMap (component s n)).toElementMap x := by
  intro n
  induction n with
  | zero =>
    intro s
    rw [← head_apply, map_rec, head_push, head_apply]
  | succ k ih =>
    intro s
    have ht : (tail V).toElementMap ((mapMap V).toElementMap (pair s x)) =
        (mapMap V).toElementMap (pair ((tail (funSpace V V)).toElementMap s) x) := by
      conv_lhs => rw [map_rec]
      rw [tail_push]
    rw [← component_tail, ht, ih, component_tail]

end DomainTheory.Neighborhood.Exercise511
