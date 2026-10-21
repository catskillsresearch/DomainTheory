/-ai
On the power set of a monoid, the operator associated with two elements sends a subset to the union of the singleton of the unit, the set of those two elements, and the pointwise product of the subset with itself.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Submonoid.Basic
import all Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
import all Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Nat.Defs
import all Mathlib.Algebra.Group.Nat.Defs

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise417

open Pointwise

open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]

/-- Scott's operator `F(x) = {1} ∪ {a, b} ∪ x · x` on `P S`. -/
def F (a b : S) (x : Set S) : Set S := {1} ∪ {a, b} ∪ x * x

end DomainTheory.NeighbourhoodSystems.Exercise417
