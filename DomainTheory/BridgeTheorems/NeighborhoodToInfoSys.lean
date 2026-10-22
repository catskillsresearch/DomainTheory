module

public import DomainTheory.BridgeTheorems.toInfoSys
public import DomainTheory.BridgeTheorems.NeighborhoodToInfoSys.domainOrderIso
public import Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.NbhdBasis
public import DomainTheory.BridgeTheorems.interOf
public import DomainTheory.BridgeTheorems.toElement
public import DomainTheory.BridgeTheorems.ofElement
public import DomainTheory.BridgeTheorems.interOf_empty
public import DomainTheory.BridgeTheorems.interOf_insert
public import DomainTheory.BridgeTheorems.nbhd_subset_master
public import DomainTheory.BridgeTheorems.interOf_singleton
public import DomainTheory.BridgeTheorems.mem_interOf
public import DomainTheory.BridgeTheorems.interOf_subset_nbhd
public import DomainTheory.BridgeTheorems.interOf_subset_master
public import DomainTheory.BridgeTheorems.interOf_anti
public import DomainTheory.BridgeTheorems.interOf_mem_of_lower_bound
public import DomainTheory.BridgeTheorems.filter_mem_interOf
public import DomainTheory.BridgeTheorems.toElement_carrier
public import DomainTheory.BridgeTheorems.ofElement_mem
public import DomainTheory.BridgeTheorems.toElement_ofElement
public import DomainTheory.BridgeTheorems.ofElement_toElement

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems
open DomainTheory.InformationSystems


namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)


end NbhdBasis

/-- Blueprint name: neighbourhood system (with decidable basis) → information system. -/
abbrev neighborhoodSystem_to_infoSys {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α) :
    InfoSys ι :=
  B.toInfoSys

end DomainTheory.BridgeTheorems
