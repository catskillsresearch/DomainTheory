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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_dualFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.dualFilter_dualFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.idealOf

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

theorem union_mem_idealOf {O Y Z : Set (ℕ → Bool)} (hY : Y ∈ idealOf O) (hZ : Z ∈ idealOf O) :
    Y ∪ Z ∈ idealOf O := ⟨hY.1.union hZ.1, Set.union_subset hY.2 hZ.2⟩

end DomainTheory.NeighbourhoodSystems
