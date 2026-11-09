module

public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp


@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

theorem wayBelowUp_bot : wayBelowUp (⊥ : D) = (Set.univ : Set D) := by
  ext z
  exact ⟨fun _ => trivial, fun _ => WayBelow.bot z⟩

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
