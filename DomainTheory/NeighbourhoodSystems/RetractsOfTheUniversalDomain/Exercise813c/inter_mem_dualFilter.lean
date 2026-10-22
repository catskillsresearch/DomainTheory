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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.dualFilter_dualFilter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- An ideal closed under (binary, hence finite) union dualizes to a filter closed under
intersection (`(Y ∩ Z)ᶜ = Yᶜ ∪ Zᶜ`, De Morgan). -/
theorem inter_mem_dualFilter {α : Type*} {x : Set (Set α)}
    (hx : ∀ Y ∈ x, ∀ Z ∈ x, Y ∪ Z ∈ x) {Y Z : Set α}
    (hY : Y ∈ dualFilter x) (hZ : Z ∈ dualFilter x) : Y ∩ Z ∈ dualFilter x := by
  have h := hx _ hY _ hZ
  simpa [dualFilter, Set.compl_inter] using h

end DomainTheory.NeighbourhoodSystems
