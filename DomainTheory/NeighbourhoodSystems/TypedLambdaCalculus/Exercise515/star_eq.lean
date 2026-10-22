module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.mem_star

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise
open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]


/-- **Scott's unfolding** `z* = Λ ∪ z·z*`. -/
theorem star_eq (z : Set S) : star z = (1 : Set S) ∪ z * star z := by
  apply Set.Subset.antisymm
  · intro s hs
    obtain ⟨n, hn⟩ := mem_star.mp hs
    cases n with
    | zero =>
        rw [kpow_zero] at hn
        rw [Set.mem_union]; exact Or.inl hn
    | succ m =>
        rw [kpow_succ, Set.mem_mul] at hn
        obtain ⟨a, ha, t, ht, rfl⟩ := hn
        rw [Set.mem_union]; right
        rw [Set.mem_mul]
        exact ⟨a, ha, t, mem_star.mpr ⟨m, ht⟩, rfl⟩
  · intro s hs
    rw [Set.mem_union] at hs
    rcases hs with h1 | h2
    · exact mem_star.mpr ⟨0, by rw [kpow_zero]; exact h1⟩
    · rw [Set.mem_mul] at h2
      obtain ⟨a, ha, t, ht, rfl⟩ := h2
      obtain ⟨m, hm⟩ := mem_star.mp ht
      exact mem_star.mpr ⟨m + 1, by rw [kpow_succ, Set.mem_mul]; exact ⟨a, ha, t, hm, rfl⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise515
