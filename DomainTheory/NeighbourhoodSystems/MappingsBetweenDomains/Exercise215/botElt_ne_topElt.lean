/-ai
The bottom element is distinct from the top element.

The empty set belongs to the top element, because it is a neighbourhood contained in itself. If the two elements were equal, membership in the bottom element would force the empty set to be the universe, and the universe is not empty.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- `⊥ ≠ ⊤` (so `⊥ ⊏ ⊤`). -/
theorem botElt_ne_topElt : botElt ≠ topElt := by
  intro h
  have htop : topElt.mem ∅ := ⟨O_mem_empty, subset_rfl⟩
  rw [← h, mem_botElt] at htop
  exact univ_ne_empty htop.symm

end DomainTheory.NeighbourhoodSystems.Exercise215
