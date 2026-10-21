/-ai
The basic neighbourhood of a finite code n is the set of elements x of Pω such that the finite set coded by n is contained in x.
ai-/
module

public import Mathlib.Topology.Bases
import all Mathlib.Topology.Bases
public import Mathlib.Topology.Order
import all Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

/-- **Scott 1976, §1, Definition.** A basic neighbourhood is
`{x ∈ Pω | e n ⊆ x}` for some finite code `n`. -/
def basicNhhd (n : ℕ) : Set Pomega := {x | e n ⊆ x}

end DomainTheory.DataTypesAsLattices
