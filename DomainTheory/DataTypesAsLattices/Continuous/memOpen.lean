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

/-- Subbasic open `{x | k ∈ x}` of the positive topology. -/
def memOpen (k : ℕ) : Set Pomega := {x | k ∈ x}

end DomainTheory.DataTypesAsLattices
