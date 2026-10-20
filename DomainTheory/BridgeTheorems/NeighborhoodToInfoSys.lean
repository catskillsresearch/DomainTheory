module

public import Mathlib.Data.Finset.Fold
import all Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.NbhdBasis
public import DomainTheory.BridgeTheorems.interOf
public import DomainTheory.BridgeTheorems.toInfoSys
public import DomainTheory.BridgeTheorems.toElement
public import DomainTheory.BridgeTheorems.ofElement
public import DomainTheory.BridgeTheorems.NeighborhoodToInfoSys.domainOrderIso
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

/-!
# Neighbourhood systems → information systems (1980 → 1982)

Scott (1982) notes that neighbourhood systems and information systems are equivalent
in a precise sense. This module realises one direction: given a neighbourhood system
presented with a **decidable index of its neighbourhoods** (a constructive coding of
`𝒟`), build an information system on those indices whose domain is order-isomorphic
to the original filter domain.

Tokens of the information system are indices of neighbourhoods; consistency is
membership of the finite intersection in `𝒟` (Scott’s empty intersection = `Δ`);
entailment is “the intersection is a neighbourhood and is contained in the target.”
-/

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems
open DomainTheory.InformationSystems


namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)













/-! ## Domain isomorphism -/








end NbhdBasis

/-- Blueprint name: neighbourhood system (with decidable basis) → information system. -/
abbrev neighborhoodSystem_to_infoSys {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α) :
    InfoSys ι :=
  B.toInfoSys

end DomainTheory.BridgeTheorems
