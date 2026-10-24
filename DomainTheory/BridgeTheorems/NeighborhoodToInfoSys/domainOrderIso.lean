module

public import DomainTheory.BridgeTheorems.toElement_ofElement
public import DomainTheory.BridgeTheorems.ofElement_toElement
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainsGivenByNeighbourhoods
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.Basic
public import Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.NbhdBasis
public import DomainTheory.BridgeTheorems.interOf_empty
public import DomainTheory.BridgeTheorems.toInfoSys
public import DomainTheory.BridgeTheorems.toElement
public import DomainTheory.BridgeTheorems.ofElement

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

/-- Order isomorphism between the neighbourhood-system domain and the induced
information-system domain. -/
def domainOrderIso : B.system.Element ≃o B.toInfoSys.Element where
  toFun := B.toElement
  invFun := B.ofElement
  left_inv := B.ofElement_toElement
  right_inv := B.toElement_ofElement
  map_rel_iff' := by
    intro x y
    constructor
    · intro h X hX
      obtain ⟨i, rfl⟩ := B.exhaustive (x.sub hX)
      have hi : i ∈ (B.toElement x).carrier := hX
      have hi' : i ∈ (B.toElement y).carrier := h hi
      exact y.up_mem hi' (x.sub hX) subset_rfl
    · intro h i hi
      exact h (B.nbhd i) hi

end NbhdBasis

end DomainTheory.BridgeTheorems
