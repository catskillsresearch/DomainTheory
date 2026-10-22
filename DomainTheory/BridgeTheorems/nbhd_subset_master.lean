/-ai
Each basis neighbourhood is contained in the master set of the neighbourhood system.

The neighbourhood belongs to the system, and every neighbourhood of the system is contained in the master set.
ai-/
module

public import Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.NbhdBasis
public import DomainTheory.BridgeTheorems.interOf_empty

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

theorem nbhd_subset_master (i : ι) : B.nbhd i ⊆ B.system.master :=
  B.system.sub_master (B.nbhd_mem i)

end NbhdBasis

end DomainTheory.BridgeTheorems
