/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise817
public import DomainTheory.Neighborhood.Proposition810b
public import DomainTheory.Neighborhood.Exercise326Sum
public import DomainTheory.Neighborhood.Exercise315
public import DomainTheory.Neighborhood.Exercise819.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u


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
end DomainTheory.Neighborhood
