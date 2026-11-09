module

public import DomainTheory.BridgeTheorems.PresentationDomains.roundFilter_infoSys_iso
public import DomainTheory.BridgeTheorems.PresentationDomains.continuousLattice_roundFilter_iso

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice
open ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D] [DecidableEq D]

noncomputable def continuousLattice_roundInfoSys_iso (hD : ContinuousLattice D) :
    D ≃o RoundInfoSysElement (D := D) :=
  (continuousLattice_roundFilter_iso hD).trans roundFilter_infoSys_iso

end DomainTheory.BridgeTheorems
