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
