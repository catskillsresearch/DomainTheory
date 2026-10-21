/-ai
A map f from Pω to Pω is Scott continuous when its value at each x equals the Scott union of f at x, that is, the union of the values of f on the finite subsets of x.
ai-/
module

public import Mathlib.Topology.Bases
import all Mathlib.Topology.Bases
public import Mathlib.Topology.Order
import all Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega
public import DomainTheory.DataTypesAsLattices.Continuous.scottUnion

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

/-- **Scott 1976, §1, Definition.** `f : Pω → Pω` is continuous iff
`f(x) = ⋃ {f(e n) | e n ⊆ x}`. -/
def IsScottContinuous (f : Pomega → Pomega) : Prop :=
  ∀ x, f x = scottUnion f x

end DomainTheory.DataTypesAsLattices
