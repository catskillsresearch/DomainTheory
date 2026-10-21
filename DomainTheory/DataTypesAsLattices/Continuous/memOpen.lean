/-ai
The subbasic open associated with a natural number k is the set of elements x of Pω such that k belongs to x.
ai-/
module

public import Mathlib.Topology.Bases
import all Mathlib.Topology.Bases
public import Mathlib.Topology.Order
import all Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

/-- Subbasic open `{x | k ∈ x}` of the positive topology. -/
def memOpen (k : ℕ) : Set Pomega := {x | k ∈ x}

end DomainTheory.DataTypesAsLattices
