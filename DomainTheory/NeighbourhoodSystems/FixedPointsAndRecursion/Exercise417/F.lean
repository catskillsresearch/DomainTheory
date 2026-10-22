module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Nat.Defs

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise417

open Pointwise

open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]

/-- Scott's operator `F(x) = {1} ∪ {a, b} ∪ x · x` on `P S`. -/
def F (a b : S) (x : Set S) : Set S := {1} ∪ {a, b} ∪ x * x

end DomainTheory.NeighbourhoodSystems.Exercise417
