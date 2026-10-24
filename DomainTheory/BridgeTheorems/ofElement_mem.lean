module

public import DomainTheory.BridgeTheorems.ofElement
public import Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainsGivenByNeighbourhoods
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.NbhdBasis
public import DomainTheory.BridgeTheorems.interOf_empty
public import DomainTheory.BridgeTheorems.toInfoSys

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

theorem ofElement_mem (e : B.toInfoSys.Element) (X : Set α) :
    (B.ofElement e).mem X ↔ B.system.mem X ∧ ∃ i ∈ e.carrier, B.nbhd i ⊆ X :=
  Iff.rfl

end NbhdBasis

end DomainTheory.BridgeTheorems
