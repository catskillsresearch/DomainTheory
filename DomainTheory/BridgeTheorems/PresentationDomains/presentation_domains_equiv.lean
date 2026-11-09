module

public import DomainTheory.BridgeTheorems.PresentationDomains.continuousLattice_roundInfoSys_iso

@[expose] public section

namespace DomainTheory.BridgeTheorems

variable {D : Type*} [CompleteLattice D] [DecidableEq D]

noncomputable def presentation_domains_equiv (hD : ContinuousLattice D) :
    D ≃o RoundInfoSysElement (D := D) :=
  continuousLattice_roundInfoSys_iso hD

end DomainTheory.BridgeTheorems
