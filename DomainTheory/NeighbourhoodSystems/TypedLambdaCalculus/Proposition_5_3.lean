module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table_5_5

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
namespace ApproximableMap

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
  ·
    apply fixElement_le_of_toElementMap_le
    rw [toElementMap_paired]
    rw [hτ, hσ]
  ·
    set fp := (paired τ σ).fixElement with hfp
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
      rw [← hfp_pair]; rw [ha]; exact this
    have hσb : σ.toElementMap (pair a b) = b := by
      have : (pair (τ.toElementMap fp) (σ.toElementMap fp)).snd = fp.snd := by rw [hfpeq]
      rw [snd_pair] at this
      rw [← hfp_pair]; rw [hb]; exact this

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
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem51

end Theorem51
end
end DomainTheory.NeighbourhoodSystems
end
