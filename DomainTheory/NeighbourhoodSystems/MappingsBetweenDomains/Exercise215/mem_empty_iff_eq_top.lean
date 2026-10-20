module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_mem_empty
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.topElt

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **The defining property of `⊤`.** An element `z` of `|𝒪|` is `⊤` iff it contains `∅`: `∅` is
the sharpest neighbourhood, so `∅ ∈ z` forces `z` to be the principal filter `↑∅ = ⊤`. -/
theorem mem_empty_iff_eq_top (z : O.Element) : z.mem ∅ ↔ z = topElt := by
  constructor
  · intro hz
    exact O.eq_principal_of_isMin z hz (fun Y _ => Set.empty_subset Y)
  · rintro rfl
    exact ⟨O_mem_empty, subset_rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise215
