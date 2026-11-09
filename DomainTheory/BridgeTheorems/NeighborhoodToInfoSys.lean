module

public import DomainTheory.BridgeTheorems.toInfoSys
public import DomainTheory.BridgeTheorems.NeighborhoodToInfoSys.domainOrderIso

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

abbrev neighborhoodSystem_to_infoSys {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α) :
    InfoSys ι :=
  B.toInfoSys

end DomainTheory.BridgeTheorems
