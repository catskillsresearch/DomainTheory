/-ai
The universe of a one-element type is not the empty set.

If the two sets were equal, the unique element would belong to the empty set, and simplification contradicts that membership.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem univ_ne_empty : (Set.univ : Set (Fin 1)) ≠ ∅ := by
  intro h
  have h0 : (0 : Fin 1) ∈ (∅ : Set (Fin 1)) := h ▸ Set.mem_univ 0
  simp at h0

end DomainTheory.NeighbourhoodSystems.Exercise215
