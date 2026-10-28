module

public import Mathlib.Data.Finset.Fold
public import DomainTheory.BridgeTheorems.NbhdBasis
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_23
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Proposition23

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

def interOf (u : Finset ι) : Set α :=
  u.fold (· ∩ ·) B.system.master B.nbhd

end NbhdBasis

end DomainTheory.BridgeTheorems
