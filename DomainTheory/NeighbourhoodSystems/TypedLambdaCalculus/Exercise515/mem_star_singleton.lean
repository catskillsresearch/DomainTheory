/-ai
A point lies in the star of the singleton of e if and only if it equals some monoid power of e.

Membership in the star is membership in some finite power. The power-of-a-singleton law converts that membership into equality with the corresponding monoid power, in both directions.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
import all Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
import all Mathlib.Algebra.FreeMonoid.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.mem_star
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.mem_kpow_singleton

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise
open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]


/-- `{e}* = e* = {Λ, e, e², …}`: a point lies in `star {e}` iff it is some power of `e`. -/
theorem mem_star_singleton (e s : S) : s ∈ star ({e} : Set S) ↔ ∃ n, s = e ^ n := by
  rw [mem_star]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_kpow_singleton e s n).mp hn⟩
  · rintro ⟨n, rfl⟩; exact ⟨n, (mem_kpow_singleton e (e ^ n) n).mpr rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise515
