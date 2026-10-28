module

public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toNeighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_23
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import DomainTheory.ContinuousLattice.WayBelow.scottOpen_wayBelow

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

abbrev Filter : Type _ :=
  (toNeighborhoodSystem : NeighborhoodSystem D).Element

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
