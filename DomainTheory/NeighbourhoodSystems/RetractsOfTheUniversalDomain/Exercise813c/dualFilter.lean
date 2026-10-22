/-ai
The dual of a family of sets is the family of those sets whose complements belong to the original family.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_genPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_box
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.toSet'_mk

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- `Y ↦ Yᶜ`, applied to a whole family: turns an ideal into (the membership predicate of) a
filter, and vice versa (`dualFilter` is its own inverse, `dualFilter_dualFilter`). -/
def dualFilter {α : Type*} (x : Set (Set α)) : Set (Set α) := {Y | Yᶜ ∈ x}

end DomainTheory.NeighbourhoodSystems
