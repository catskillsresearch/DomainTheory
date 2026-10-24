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


/-- `{1}` is a fixed point of `F 1 1`: `{1} ∪ {1, 1} ∪ {1}·{1} = {1}`. -/
theorem F_one_one_singleton : F (1 : ℕ) 1 ({1} : Set ℕ) = {1} := by
  unfold F
  rw [Set.singleton_mul_singleton]
  simp

end DomainTheory.NeighbourhoodSystems.Exercise417
