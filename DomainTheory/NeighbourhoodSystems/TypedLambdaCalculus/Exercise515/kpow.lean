/-ai
The n-th pointwise power of a set z is defined by iteration: the zeroth power is the unit set, and the successor power is the pointwise product of z with the preceding power.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
import all Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
import all Mathlib.Algebra.FreeMonoid.Basic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise

open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]

/-- `zⁿ` as an iterated pointwise product (left-recursion `z^{n+1} = z·zⁿ`). -/
def kpow (z : Set S) : ℕ → Set S
  | 0 => 1
  | n + 1 => z * kpow z n

end DomainTheory.NeighbourhoodSystems.Exercise515
