/-ai
The way-below neighbourhood of an element a of a complete lattice is the set of elements way-below which a lies.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

/-- `↟a = { z | a ≪ z }`. -/
def wayBelowUp (a : D) : Set D := {z | a ≪ z}

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
