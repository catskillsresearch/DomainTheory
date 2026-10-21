/-ai
The star of a set z is the set of points that lie in some finite pointwise power of z, including the empty product, which is the unit.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
import all Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
import all Mathlib.Algebra.FreeMonoid.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.kpow
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.kpow_zero
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.kpow_succ

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise

open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]

/-- Scott's `z*`: the set of all finite products of elements of `z` (including the empty product
`1`). Defined as `{s ∣ ∃ n, s ∈ zⁿ}` to stay choice-free (avoiding `⋃` order lemmas). -/
def star (z : Set S) : Set S := {s | ∃ n, s ∈ kpow z n}

end DomainTheory.NeighbourhoodSystems.Exercise515
