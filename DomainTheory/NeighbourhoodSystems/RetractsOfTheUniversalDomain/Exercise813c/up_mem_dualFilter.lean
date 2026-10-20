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

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

/-- An ideal downward-closed within `GeneratedBy g` dualizes to a filter upward-closed within
`GeneratedBy g` (De Morgan again: `Z ⊆ Y ↔ Yᶜ ⊆ Zᶜ`). -/
theorem up_mem_dualFilter {α : Type*} {g : ℕ → Set α} {x : Set (Set α)}
    (hx : ∀ Y ∈ x, ∀ Z, GeneratedBy g Z → Z ⊆ Y → Z ∈ x) {Y Z : Set α}
    (hY : Y ∈ dualFilter x) (hZg : GeneratedBy g Z) (hYZ : Y ⊆ Z) : Z ∈ dualFilter x := by
  have hcompl : Zᶜ ⊆ Yᶜ := Set.compl_subset_compl.mpr hYZ
  simpa [dualFilter] using hx _ hY _ hZg.compl hcompl

end DomainTheory.NeighbourhoodSystems
