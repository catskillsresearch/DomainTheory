/-ai
An effective isomorphism determines a domain isomorphism by sending each element along the element map of the forward approximable map, with inverse the element map of the inverse approximable map. The left and right inverse laws rewrite composition of element maps by the effective inverse laws and the element map of the identity. The order law uses monotonicity of the forward element map in one direction and, in the other, monotonicity of the inverse element map followed by the left inverse.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.NeighborhoodSystemu2eIsEffectivelyGivenu2etoS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashMap_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProju2080_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProju2081_isComputable
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

namespace EffectiveIso

variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
  {P : ComputablePresentation V} {Q : ComputablePresentation W}

/-- An effective isomorphism is in particular a domain isomorphism (`|D| ≃o |E|`): the elementwise
maps are mutually inverse (from `left_inv`/`right_inv` via `toElementMap_comp`/`toElementMap_idMap`)
and each is monotone (`toElementMap_mono`), so they reflect as well as preserve `⊑`. -/
def toDomainIso (e : EffectiveIso P Q) : DomainIso V W where
  toFun := e.toMap.toElementMap
  invFun := e.invMap.toElementMap
  left_inv x := by
    rw [← toElementMap_comp, e.left_inv, toElementMap_idMap]
  right_inv y := by
    rw [← toElementMap_comp, e.right_inv, toElementMap_idMap]
  map_rel_iff' := by
    intro x y
    show e.toMap.toElementMap x ≤ e.toMap.toElementMap y ↔ x ≤ y
    refine ⟨fun h => ?_, fun h => e.toMap.toElementMap_mono h⟩
    have hmono := e.invMap.toElementMap_mono h
    rwa [← toElementMap_comp, ← toElementMap_comp, e.left_inv, toElementMap_idMap,
      toElementMap_idMap] at hmono

end EffectiveIso

end Exercise718

end DomainTheory.NeighbourhoodSystems
