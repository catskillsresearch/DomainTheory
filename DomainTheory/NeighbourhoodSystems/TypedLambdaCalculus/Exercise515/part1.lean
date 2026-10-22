module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.arden

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise
open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]


/-- **Exercise 5.15(1).** The least fixed point of `z = {e}·z ∪ {e'}` is `e*·{e'}` (`star {e}` is
`e*` by `mem_star_singleton`). -/
theorem part1 (e e' : S) :
    lfpSet (fun w => ({e} : Set S) * w ∪ {e'}) = star ({e} : Set S) * {e'} := by
  have hG : (fun w => ({e} : Set S) * w ∪ {e'}) = G ({e} : Set S) {e'} := rfl
  rw [hG]; exact arden {e} {e'}

end DomainTheory.NeighbourhoodSystems.Exercise515
