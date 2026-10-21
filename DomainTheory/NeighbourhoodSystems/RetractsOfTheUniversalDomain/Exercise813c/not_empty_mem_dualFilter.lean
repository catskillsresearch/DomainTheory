/-ai
If a family of sets excludes the whole carrier, then its dual excludes the empty set.

Simplifying the definition of the dual, membership of the empty set would be membership of the whole carrier.
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

/-- An ideal excluding `univ` dualizes to a filter excluding `∅`. -/
theorem not_empty_mem_dualFilter {α : Type*} {x : Set (Set α)} (h : Set.univ ∉ x) :
    (∅ : Set α) ∉ dualFilter x := by simpa [dualFilter] using h

end DomainTheory.NeighbourhoodSystems
