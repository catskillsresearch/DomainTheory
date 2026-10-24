module

public import DomainTheory.BridgeTheorems.interOf
public import DomainTheory.BridgeTheorems.mem_interOf
public import Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainsGivenByNeighbourhoods
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

theorem interOf_subset_nbhd {u : Finset ι} {i : ι} (hi : i ∈ u) :
    B.interOf u ⊆ B.nbhd i := fun _ hx => (B.mem_interOf.mp hx).2 i hi

end NbhdBasis

end DomainTheory.BridgeTheorems
