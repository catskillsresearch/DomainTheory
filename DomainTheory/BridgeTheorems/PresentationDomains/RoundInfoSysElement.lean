module

public import DomainTheory.BridgeTheorems.PresentationDomains.IsRoundInfoSysElement

@[expose] public section

namespace DomainTheory.BridgeTheorems

variable {D : Type*} [CompleteLattice D] [DecidableEq D]

abbrev RoundInfoSysElement : Type _ :=
  { e : (wayBelowNbhdBasis (D := D)).toInfoSys.Element // IsRoundInfoSysElement (D := D) e }

end DomainTheory.BridgeTheorems
