/-ai
The dual of the dual of a family of sets is the family itself.

Extending a set and simplifying the definition of the dual cancels the two complements.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_genPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_box
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.toSet'_mk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.dualFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_dualFilter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

@[simp] theorem dualFilter_dualFilter {α : Type*} (x : Set (Set α)) :
    dualFilter (dualFilter x) = x := by
  ext Y; simp [dualFilter]

end DomainTheory.NeighbourhoodSystems
