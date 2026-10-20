/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition68
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Theorem69.Basic
import DomainTheory.Neighborhood.Theorem69.isStrict_of_comp_eq_id
import DomainTheory.Neighborhood.Theorem69.toStrictFilter_toStrictMap
import DomainTheory.Neighborhood.Theorem69.homOp_apply_filter


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise510

universe u

variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}









/-- **Theorem 6.9 (Scott 1981, PRG-19).** If `T` is continuous on maps and `D ≅ T(D)` (so `D` is a
`T`-algebra via `i : T(D) → D`), then for any `T`-algebra `B = (E, k)` with `k` strict there is a
homomorphism `D → E`. The homomorphism is the least fixed point of `λh. k ∘ T(h) ∘ j`. -/
theorem nonempty_algHom_of_continuousOnMaps
    (T : Endofunctor DomainObj) (hT : ContinuousOnMaps T)
    {D : DomainObj} (iso : Iso (T.obj D) D)
    (B : TAlgebra T) (hk : IsStrict B.str) :
    Nonempty {g : AlgHom (⟨D, iso.hom⟩ : TAlgebra T) B // IsStrict g.hom} := by
  -- `j = i⁻¹` is strict (it is an isomorphism of domains).
  have hji : iso.inv.comp iso.hom = idMap (T.obj D).sys := iso.hom_inv_id
  have hj : IsStrict iso.inv := isStrict_of_comp_eq_id hji
  -- Definition 6.8's witness that `λf. T(f)` is approximable.
  obtain ⟨Φ, hΦ⟩ := hT D B.carrier
  -- the operator `Op = (k ∘ · ∘ j) ∘ T` and its least fixed point.
  set Op := (homOp T D B.carrier iso.inv B.str hj hk).comp Φ with hOp
  set x := Op.fixElement with hx
  set h := toStrictMap x with hh
  let Tg : StrictMap (T.obj D).sys (T.obj B.carrier).sys :=
    ⟨T.map (X := D) (Y := B.carrier) h.1, hT.isStrict_map (D := D) (E := B.carrier) h⟩
  have hfix : Op.toElementMap x = x := toElementMap_fixElement Op
  have hxh : toStrictFilter h = x := toStrictFilter_toStrictMap x
  -- `Φ` sends `h` to the filter of `T(h)`.
  have hTg : toStrictMap (Φ.toElementMap (toStrictFilter h)) = Tg := Subtype.ext (hΦ h)
  have hφ : Φ.toElementMap (toStrictFilter h) = toStrictFilter Tg := by
    rw [← hTg]; exact (toStrictFilter_toStrictMap _).symm
  -- evaluate the operator at the fixed point.
  have hOpx : Op.toElementMap x
      = toStrictFilter (homOpComp T D B.carrier iso.inv B.str hj hk Tg) := by
    rw [hOp, toElementMap_comp, ← hxh, hφ, homOp_apply_filter]
  have hcompeq : toStrictFilter (homOpComp T D B.carrier iso.inv B.str hj hk Tg)
      = toStrictFilter h := by
    rw [← hOpx, hfix, hxh]
  have hh' : homOpComp T D B.carrier iso.inv B.str hj hk Tg = h := by
    have h2 := congrArg toStrictMap hcompeq
    rwa [toStrictMap_toStrictFilter, toStrictMap_toStrictFilter] at h2
  -- the fixed-point equation `h = k ∘ T(h) ∘ j`.
  have hcore : B.str.comp ((T.map (X := D) (Y := B.carrier) h.1).comp iso.inv) = h.1 :=
    congrArg Subtype.val hh'
  -- rearrange to the homomorphism square `h ∘ i = k ∘ T(h)`.
  refine ⟨⟨{ hom := h.1, comm := ?_ }, h.2⟩⟩
  show h.1.comp iso.hom = B.str.comp (T.map (X := D) (Y := B.carrier) h.1)
  conv_lhs => rw [← hcore]
  rw [comp_assoc, comp_assoc, hji, comp_idMap]

end DomainTheory.Neighborhood
