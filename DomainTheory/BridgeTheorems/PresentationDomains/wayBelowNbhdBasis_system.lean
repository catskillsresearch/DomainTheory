module
public import DomainTheory.BridgeTheorems.PresentationDomains.wayBelowNbhdBasis

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.ContinuousLattice
open DomainTheory.NeighbourhoodSystems
open Order
open scoped DomainTheory.ContinuousLattice
open ContinuousLatticeToNeighborhood

universe u
variable {D : Type u} [CompleteLattice D] [DecidableEq D]

theorem wayBelowNbhdBasis_system :
    (wayBelowNbhdBasis (D := D)).system = toNeighborhoodSystem :=
  rfl

end DomainTheory.BridgeTheorems
