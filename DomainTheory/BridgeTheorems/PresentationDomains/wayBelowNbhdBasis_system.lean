module
public import DomainTheory.BridgeTheorems.PresentationDomains.wayBelowNbhdBasis

@[expose] public section

namespace DomainTheory.BridgeTheorems

open ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D] [DecidableEq D]

theorem wayBelowNbhdBasis_system :
    (wayBelowNbhdBasis (D := D)).system = toNeighborhoodSystem :=
  rfl

end DomainTheory.BridgeTheorems
