module

public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.codes

public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp_bot

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

theorem bot_mem_codes (f : Filter (D := D)) : (⊥ : D) ∈ codes f := by
  have : f.mem (wayBelowUp (⊥ : D)) := by
    rw [wayBelowUp_bot]
    exact f.master_mem
  exact this

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
