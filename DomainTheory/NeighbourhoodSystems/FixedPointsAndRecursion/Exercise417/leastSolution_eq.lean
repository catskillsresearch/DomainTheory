/-ai
The least fixed-point set of the monoid power-set operator solves the operator equation.

The operator is monotone, and the least-fixed-point construction sends a monotone operator to a fixed point.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Nat.Defs
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise417.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise417.F_monotone

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.lfpSet_isFixed
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise417

open Pointwise
open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]


/-- The least solution `lfpSet (F a b)` indeed solves Scott's equation `x = {1} ∪ {a, b} ∪ x · x`. -/
theorem leastSolution_eq (a b : S) :
    F a b (lfpSet (F a b)) = lfpSet (F a b) :=
  lfpSet_isFixed (F a b) (F_monotone a b)

end DomainTheory.NeighbourhoodSystems.Exercise417
