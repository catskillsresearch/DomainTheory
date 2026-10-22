/-ai
The set of codes of a filter is a lower set: if b lies under a code a, then b is a code.

The way-below neighbourhood of a belongs to the filter. Way-below neighbourhoods reverse the order, so that neighbourhood is contained in the way-below neighbourhood of b, and the filter is closed upward under that containment.
ai-/
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
