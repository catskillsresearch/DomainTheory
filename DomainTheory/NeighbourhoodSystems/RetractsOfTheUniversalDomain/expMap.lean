module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_9

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

/-- **The Hom-functor's action on maps**, `f ↦ k∘f∘h`, transported to the function-space
neighbourhood systems via `curry`/`evalMap`/`prodMap`, exactly as `lamComb` does for the
self-map case. -/
noncomputable def expMap {γ δ γ' δ' : Type*} {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}
    {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}
    (h : ApproximableMap V0' V0) (k : ApproximableMap V1 V1') :
    ApproximableMap (funSpace V0 V1) (funSpace V0' V1') :=
  curry (k.comp ((evalMap V0 V1).comp (prodMap (idMap (funSpace V0 V1)) h)))

namespace expMap

variable {γ δ γ' δ' γ'' δ'' : Type*}
variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}
variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}
variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}

theorem eq (h : ApproximableMap V0' V0) (k : ApproximableMap V1 V1') :
    expMap h k = curry (k.comp ((evalMap V0 V1).comp (prodMap (idMap (funSpace V0 V1)) h))) := rfl

/-- `expMap` specializes to `lamComb` on self-maps of `𝒰`. -/
theorem eq_lamComb (a b : ApproximableMap U U) : expMap a b = lamComb a b := rfl

/-- **`expMap h k`, transported through `funSpaceEquiv`, is exactly `f ↦ k∘f∘h`.** -/
theorem toApproxMap_toElementMap (h : ApproximableMap V0' V0) (k : ApproximableMap V1 V1')
    (φ : (funSpace V0 V1).Element) :
    toApproxMap ((expMap h k).toElementMap φ) = k.comp ((toApproxMap φ).comp h) := by
  apply ext_of_toElementMap
  intro z
  rw [eq, toElementMap_curry_apply, toElementMap_comp, toElementMap_comp,
    toElementMap_prodMap_pair, toElementMap_idMap, evalMap_apply, toElementMap_comp,
    toElementMap_comp]

/-- **`expMap` preserves composition, contravariantly in `h`.** -/
theorem comp (h : ApproximableMap V0' V0) (k : ApproximableMap V1 V1')
    (h' : ApproximableMap V0'' V0') (k' : ApproximableMap V1' V1'') :
    expMap (h.comp h') (k'.comp k) = (expMap h' k').comp (expMap h k) := by
  apply ext_of_toElementMap
  intro φ
  apply (funSpaceEquiv V0'' V1'').injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toApproxMap_toElementMap, toElementMap_comp,
    toApproxMap_toElementMap, toApproxMap_toElementMap]
  simp only [comp_assoc]

/-- **`expMap` preserves identities: `expMap I I = I`.** -/
theorem id : expMap (idMap V0) (idMap V1) = idMap (funSpace V0 V1) := by
  apply ext_of_toElementMap
  intro φ
  apply (funSpaceEquiv V0 V1).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toElementMap_idMap,
    toApproxMap_toElementMap, comp_idMap, idMap_comp]

/-- **`expMap` is monotone in its contravariant argument** (`k` fixed). -/
theorem mono_left {h h' : ApproximableMap V0' V0} (hh : h ≤ h') (k : ApproximableMap V1 V1') :
    expMap h k ≤ expMap h' k := by
  rw [le_iff_toElementMap_le]
  intro φ
  apply (funSpaceEquiv V0' V1').map_rel_iff.mp
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toApproxMap_toElementMap,
    toApproxMap_toElementMap]
  exact comp_mono_gen le_rfl (comp_mono_gen le_rfl hh)

end expMap

end DomainTheory.NeighbourhoodSystems
