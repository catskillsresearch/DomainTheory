/-ai
If a family of sets contains the empty set, then its dual contains the whole carrier.

Simplifying the definition of the dual, the complement of the whole carrier is empty.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
import all Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
import all Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
import all Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_genPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_box
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.toSet'_mk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.dualFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_dualFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.dualFilter_dualFilter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- An ideal containing `∅` dualizes to a filter containing `univ`. -/
theorem univ_mem_dualFilter {α : Type*} {x : Set (Set α)} (h : (∅ : Set α) ∈ x) :
    Set.univ ∈ dualFilter x := by simpa [dualFilter] using h

end DomainTheory.NeighbourhoodSystems
