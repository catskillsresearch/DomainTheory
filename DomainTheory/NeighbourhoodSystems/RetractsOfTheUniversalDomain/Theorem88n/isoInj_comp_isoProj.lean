/-ai
The composite of the code-level injection after the code-level projection is the identity map on the coded copy.

Compare the maps by their actions on elements. The element map of a composite is the composite of the element maps. Unfolding both maps, the element map of the isomorphism construction, applied after the element map of the inverse, is the identity by the order-isomorphism law, which is the element map of the identity map.
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


/-- `isoInj ∘ isoProj = I_D''`. -/
theorem isoInj_comp_isoProj : (isoInj P).comp (isoProj P) = idMap (DprimeUCode P) := by
  apply ext_of_toElementMap
  intro y
  rw [toElementMap_comp]
  show (isoInj P).toElementMap ((isoProj P).toElementMap y) = _
  rw [isoInj, isoProj, toElementMap_ofIso, toElementMap_ofIso, OrderIso.apply_symm_apply,
    toElementMap_idMap]

end DomainTheory.NeighbourhoodSystems
