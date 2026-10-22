/-ai
The carrier of the information-system element produced by toElement from a filter is the set of indices whose basis neighbourhoods belong to the filter.

This is the definition of that carrier.
ai-/
module

public import Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.NbhdBasis
public import DomainTheory.BridgeTheorems.interOf_empty
public import DomainTheory.BridgeTheorems.toElement

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
