module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Combinators
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.prodEquiv

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap

def secFixX (τ : ApproximableMap (prod V₀ V₁) V₀) : ApproximableMap V₁ V₀ :=
  (fixMap V₀).comp (curry (τ.comp (swapC V₁ V₀)))

def outerOp (τ : ApproximableMap (prod V₀ V₁) V₀) (σ : ApproximableMap (prod V₀ V₁) V₁) :
    ApproximableMap V₁ V₁ :=
  σ.comp (paired (secFixX τ) (idMap V₁))

def sectionX (τ : ApproximableMap (prod V₀ V₁) V₀) (y : V₁.Element) : ApproximableMap V₀ V₀ :=
  toApproxMap ((curry (τ.comp (swapC V₁ V₀))).toElementMap y)

theorem outerOp_apply (τ : ApproximableMap (prod V₀ V₁) V₀) (σ : ApproximableMap (prod V₀ V₁) V₁)
    (y : V₁.Element) :
    (outerOp τ σ).toElementMap y = σ.toElementMap (pair ((secFixX τ).toElementMap y) y) := by
  rw [outerOp, toElementMap_comp, toElementMap_paired, toElementMap_idMap]

theorem secFixX_apply (τ : ApproximableMap (prod V₀ V₁) V₀) (y : V₁.Element) :
    (secFixX τ).toElementMap y = (sectionX τ y).fixElement := by
  rw [secFixX, toElementMap_comp, fixMap_toElementMap, sectionX]

theorem sectionX_apply (τ : ApproximableMap (prod V₀ V₁) V₀) (y : V₁.Element) (x : V₀.Element) :
    (sectionX τ y).toElementMap x = τ.toElementMap (pair x y) := by
  rw [sectionX, toElementMap_curry_apply, toElementMap_comp, swapC_apply]

theorem secFixX_isFixed (τ : ApproximableMap (prod V₀ V₁) V₀) (y : V₁.Element) :
    τ.toElementMap (pair ((secFixX τ).toElementMap y) y) = (secFixX τ).toElementMap y := by
  rw [secFixX_apply, ← sectionX_apply, toElementMap_fixElement]

/-- Least fixed point of a paired pair of binary maps is the sectional pair
`(secFixX τ (outerOp τ σ).fixElement, (outerOp τ σ).fixElement)`. -/
theorem fixElement_paired_eq (τ : ApproximableMap (prod V₀ V₁) V₀)
    (σ : ApproximableMap (prod V₀ V₁) V₁) :
    (paired τ σ).fixElement =
      pair ((secFixX τ).toElementMap (outerOp τ σ).fixElement) (outerOp τ σ).fixElement := by
  set ystar := (outerOp τ σ).fixElement with hystar
  set xstar := (secFixX τ).toElementMap ystar with hxstar
  have hσ : σ.toElementMap (pair xstar ystar) = ystar := by
    have := toElementMap_fixElement (outerOp τ σ)
    rw [← hystar] at this
    rw [outerOp_apply] at this
    rw [hxstar]; exact this
  have hτ : τ.toElementMap (pair xstar ystar) = xstar := by
    rw [hxstar]; exact secFixX_isFixed τ ystar
  apply le_antisymm
  · apply fixElement_le_of_toElementMap_le
    rw [toElementMap_paired, hτ, hσ]
  · set fp := (paired τ σ).fixElement with hfp
    set a := fp.fst with ha
    set b := fp.snd with hb
    have hfpeq : pair (τ.toElementMap fp) (σ.toElementMap fp) = fp := by
      have := toElementMap_fixElement (paired τ σ)
      rw [← hfp, toElementMap_paired] at this
      exact this
    have hfp_pair : fp = pair a b := (pair_fst_snd fp).symm
    have hτa : τ.toElementMap (pair a b) = a := by
      have : (pair (τ.toElementMap fp) (σ.toElementMap fp)).fst = fp.fst := by rw [hfpeq]
      rw [fst_pair] at this
      rw [← hfp_pair, ha]; exact this
    have hσb : σ.toElementMap (pair a b) = b := by
      have : (pair (τ.toElementMap fp) (σ.toElementMap fp)).snd = fp.snd := by rw [hfpeq]
      rw [snd_pair] at this
      rw [← hfp_pair, hb]; exact this
    have hxfix_le : (secFixX τ).toElementMap b ≤ a := by
      rw [secFixX_apply]
      apply fixElement_le_of_toElementMap_le
      rw [sectionX_apply]
      exact le_of_eq hτa
    have houter_le : (outerOp τ σ).toElementMap b ≤ b := by
      rw [outerOp_apply]
      calc σ.toElementMap (pair ((secFixX τ).toElementMap b) b)
          ≤ σ.toElementMap (pair a b) :=
            σ.toElementMap_mono (pair_le_pair_iff.mpr ⟨hxfix_le, le_refl b⟩)
        _ = b := hσb
    have hystar_le : ystar ≤ b := by
      rw [hystar]
      exact fixElement_le_of_toElementMap_le (outerOp τ σ) houter_le
    have hxstar_le : xstar ≤ a := by
      rw [hxstar]
      calc (secFixX τ).toElementMap ystar
          ≤ (secFixX τ).toElementMap b := (secFixX τ).toElementMap_mono hystar_le
        _ ≤ a := hxfix_le
    rw [hfp_pair]
    exact pair_le_pair_iff.mpr ⟨hxstar_le, hystar_le⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
