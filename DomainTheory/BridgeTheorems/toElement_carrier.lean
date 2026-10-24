module

public import DomainTheory.BridgeTheorems.toElement
public import Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_23
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

theorem toElement_carrier (x : B.system.Element) :
    (B.toElement x).carrier = {i | x.mem (B.nbhd i)} := rfl

end NbhdBasis

end DomainTheory.BridgeTheorems
