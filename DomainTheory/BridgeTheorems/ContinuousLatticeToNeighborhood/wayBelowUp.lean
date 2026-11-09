module
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import DomainTheory.ContinuousLattice.WayBelow.WayBelow

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.GreedyEnum

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

def wayBelowUp (a : D) : Set D := {z | a ≪ z}

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
