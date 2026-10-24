module

public import DomainTheory.BridgeTheorems.interOf
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

theorem interOf_insert {a : ι} {s : Finset ι} (ha : a ∉ s) :
    B.interOf (insert a s) = B.nbhd a ∩ B.interOf s :=
  Finset.fold_insert (op := (· ∩ ·)) ha

end NbhdBasis

end DomainTheory.BridgeTheorems
