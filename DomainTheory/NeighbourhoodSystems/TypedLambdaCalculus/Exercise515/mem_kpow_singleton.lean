/-ai
A point lies in the n-th power of the singleton of e if and only if it equals the n-th monoid power of e.

The argument is induction on n. At zero, the zeroth power is the unit and the zeroth monoid power is the identity, so membership in the unit decides the claim. At a successor, membership in a product and the successor law for monoid powers reduce both directions to the inductive hypothesis on the second factor, using that the first factor of a singleton product is e.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise
open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]


/-- `{e}ⁿ = {eⁿ}` at the membership level (choice-free). -/
theorem mem_kpow_singleton (e s : S) (n : ℕ) : s ∈ kpow ({e} : Set S) n ↔ s = e ^ n := by
  induction n generalizing s with
  | zero => rw [kpow_zero, pow_zero]; exact Set.mem_one
  | succ m ih =>
      rw [kpow_succ, pow_succ', Set.mem_mul]
      constructor
      · rintro ⟨a, ha, t, ht, rfl⟩
        rw [Set.mem_singleton_iff] at ha
        rw [(ih t).mp ht, ha]
      · rintro rfl
        exact ⟨e, Set.mem_singleton_iff.mpr rfl, e ^ m, (ih (e ^ m)).mpr rfl, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise515
