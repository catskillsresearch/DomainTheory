/-ai
The order isomorphism between the filter domain of a neighbourhood basis and the domain of the induced information system sends a filter to the element whose tokens are the indices of neighbourhoods belonging to the filter, and sends an element back to the filter it determines. The two composites are the identity. If the element of a filter x is contained in the element of a filter y and a neighbourhood X belongs to x, exhaustiveness writes X as the neighbourhood of some index, that index belongs to the element of x and hence of y, and upward closure of y along the equality puts X in y. Conversely, if x lies under y as filters and an index belongs to the element of x, then the neighbourhood of that index belongs to x and hence to y.
ai-/
module

public import Mathlib.Data.Finset.Fold
import all Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.NbhdBasis
public import DomainTheory.BridgeTheorems.interOf_empty
public import DomainTheory.BridgeTheorems.toInfoSys
public import DomainTheory.BridgeTheorems.toElement
public import DomainTheory.BridgeTheorems.ofElement
public import DomainTheory.BridgeTheorems.toElement_ofElement
public import DomainTheory.BridgeTheorems.ofElement_toElement

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
