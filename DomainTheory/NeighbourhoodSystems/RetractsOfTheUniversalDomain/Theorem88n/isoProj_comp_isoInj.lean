/-ai
The composite of the code-level projection after the code-level injection is the identity map on the neighbourhood system.

Compare the maps by their actions on elements. The element map of a composite is the composite of the element maps. Unfolding both maps, the element map of the inverse isomorphism, applied after the element map of the isomorphism, is the identity by the order-isomorphism law, which is the element map of the identity map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_inj_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_proj_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_projectionPair_isComputable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88n.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)




/-- `isoProj ∘ isoInj = I_D` (Theorem 2.7's `toElementMap_ofIso`, both ways, plus `OrderIso.symm_apply_apply`). -/
theorem isoProj_comp_isoInj : (isoProj P).comp (isoInj P) = idMap D := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp]
  show (isoProj P).toElementMap ((isoInj P).toElementMap x) = _
  rw [isoInj, isoProj, toElementMap_ofIso, toElementMap_ofIso, OrderIso.symm_apply_apply,
    toElementMap_idMap]

end DomainTheory.NeighbourhoodSystems
