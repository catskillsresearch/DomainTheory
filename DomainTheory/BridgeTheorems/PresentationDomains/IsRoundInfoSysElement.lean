module

public import DomainTheory.BridgeTheorems.PresentationDomains.wayBelowNbhdBasis
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Round
public import DomainTheory.BridgeTheorems.NeighborhoodToInfoSys.domainOrderIso

@[expose] public section

namespace DomainTheory.BridgeTheorems

open ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D] [DecidableEq D]

class IsRoundInfoSysElement (e : (wayBelowNbhdBasis (D := D)).toInfoSys.Element) : Prop where
  out : Round ((wayBelowNbhdBasis (D := D)).domainOrderIso.symm e)

end DomainTheory.BridgeTheorems
