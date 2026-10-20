/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition83
public import DomainTheory.Neighborhood.ApproximableExercises
public import DomainTheory.Neighborhood.Theorem85.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}






section HardDirection

variable {a : ApproximableMap E E}

/-- Idempotency of a retraction at the element level: `a(a(z)) = a(z)`. -/
theorem toElementMap_idem {a : ApproximableMap E E} (ha : IsRetraction a) (z : E.Element) :
    a.toElementMap (a.toElementMap z) = a.toElementMap z := by
  rw [← toElementMap_comp a a z, ha]

end HardDirection
end DomainTheory.Neighborhood
