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


/-- In any monoid, `Set.univ` is a fixed point of `F a b`: `s = 1 · s ∈ univ · univ`. -/
theorem F_univ (a b : S) : F a b (Set.univ : Set S) = Set.univ := by
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro s _
  exact self_mul_subset_F a b _ (Set.mem_mul.mpr ⟨1, trivial, s, trivial, one_mul s⟩)

end DomainTheory.NeighbourhoodSystems.Exercise417
