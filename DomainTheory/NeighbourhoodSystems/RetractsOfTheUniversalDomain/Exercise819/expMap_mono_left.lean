module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


section General

variable {α β γ δ : Type*}

/-- **`expMap` is monotone in its contravariant argument** (`k` fixed): `h ≤ h' ⟹ expMap h k ≤
expMap h' k`. Proved choice-freely from `comp_mono_gen` and the order-isomorphism `funSpaceEquiv`,
transported through the elementwise formula `toApproxMap_toElementMap_expMap`. -/
theorem expMap_mono_left {V0 : NeighborhoodSystem α} {V1 : NeighborhoodSystem β}
    {V0' : NeighborhoodSystem γ} {V1' : NeighborhoodSystem δ}
    {h h' : ApproximableMap V0' V0} (hh : h ≤ h') (k : ApproximableMap V1 V1') :
    expMap h k ≤ expMap h' k := by
  rw [le_iff_toElementMap_le]
  intro φ
  apply (funSpaceEquiv V0' V1').map_rel_iff.mp
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toApproxMap_toElementMap_expMap,
    toApproxMap_toElementMap_expMap]
  exact comp_mono_gen le_rfl (comp_mono_gen le_rfl hh)

end General
end DomainTheory.NeighbourhoodSystems
