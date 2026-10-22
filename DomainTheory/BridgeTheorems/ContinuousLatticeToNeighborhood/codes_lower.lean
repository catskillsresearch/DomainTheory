module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Basic

@[expose] public section


namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice
open DomainTheory.NeighbourhoodSystems
open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]


theorem codes_lower (f : Filter (D := D)) {a b : D} (hba : b ≤ a)
    (ha : a ∈ codes f) : b ∈ codes f :=
  f.up_mem ha ⟨b, rfl⟩ (wayBelowUp_anti hba)

end ContinuousLatticeToNeighborhood
end DomainTheory.BridgeTheorems
