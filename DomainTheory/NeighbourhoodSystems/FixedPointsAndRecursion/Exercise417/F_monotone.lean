module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Nat.Defs
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise417.F
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise417.preFixSubmonoid
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise417.base_subset_F
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise417.self_mul_subset_F
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise417.one_mem_F

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise417

open Pointwise
open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]


theorem F_monotone (a b : S) : Monotone (F a b) := by
  intro x y hxy
  exact Set.union_subset_union (le_refl _) (Set.mul_subset_mul hxy hxy)

end DomainTheory.NeighbourhoodSystems.Exercise417
