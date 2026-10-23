module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega.pair

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

/-- Subbasic open `{x | k ∈ x}` of the positive topology. -/
def memOpen (k : ℕ) : Set Pomega := {x | k ∈ x}

end DomainTheory.DataTypesAsLattices
