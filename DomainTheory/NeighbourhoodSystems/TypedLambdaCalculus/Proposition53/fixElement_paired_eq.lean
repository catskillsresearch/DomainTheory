/-ai
Proposition 5.3 (Scott 1981, PRG-19), Bekić's theorem, states that the least fixed point of the paired map of τ and σ is the pair whose first coordinate is the nested fixed-point map of τ at the least fixed point of the outer operator, and whose second coordinate is that least fixed point.

Let ystar be the least fixed point of the outer operator and xstar the nested map at ystar. The fixed-point equation of the outer operator, rewritten by its application law, gives the value of σ at the pair of xstar and ystar equal to ystar, and the nested fixed-point identity gives the value of τ at that pair equal to xstar, so the pair is a fixed point of the paired map and the least fixed point lies below it. Conversely, write the least fixed point as the pair of its components a and b. The fixed-point equation of the paired map, decomposed on the two components, gives τ at the pair of a and b equal to a and σ at that pair equal to b. The nested map at b lies below a, because the section at b fixes a. The outer operator at b then lies below b by its application law, monotonicity of σ, and that bound. Hence ystar lies below b, and xstar lies below a by monotonicity of the nested map together with the previous bound, so the pair of xstar and ystar lies below the pair of a and b.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition53.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition53.sectionX_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition53.secFixX_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition53.secFixX_isFixed
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition53.outerOp_apply

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap




/-- **Proposition 5.3 (Scott 1981, PRG-19).** Bekić's theorem: the least fixed point of
`F = ⟨τ, σ⟩` is the pair `⟨!x.τ(x, !y.σ(x,y)-coordinate), !y.σ(!x.τ(x,y), y)⟩`. Here the second
coordinate is `ystar = (outerOp τ σ).fixElement` and the first is `xstar = secFixX τ (ystar)`. -/
theorem fixElement_paired_eq (τ : ApproximableMap (prod V₀ V₁) V₀)
    (σ : ApproximableMap (prod V₀ V₁) V₁) :
    (paired τ σ).fixElement =
      pair ((secFixX τ).toElementMap (outerOp τ σ).fixElement) (outerOp τ σ).fixElement := by
  set ystar := (outerOp τ σ).fixElement with hystar
  set xstar := (secFixX τ).toElementMap ystar with hxstar
  -- `σ(xstar, ystar) = ystar`: `ystar` is the fixed point of `outerOp`.
  have hσ : σ.toElementMap (pair xstar ystar) = ystar := by
    have := toElementMap_fixElement (outerOp τ σ)
    rw [← hystar] at this
    rw [outerOp_apply] at this
    rw [hxstar]; exact this
  -- `τ(xstar, ystar) = xstar`: `xstar = !x.τ(x, ystar)` is a fixed point of its section.
  have hτ : τ.toElementMap (pair xstar ystar) = xstar := by
    rw [hxstar]; exact secFixX_isFixed τ ystar
  apply le_antisymm
  · -- `F.fixElement ⊑ ⟨xstar, ystar⟩`: the pair is a fixed point of `F`.
    apply fixElement_le_of_toElementMap_le
    rw [toElementMap_paired]
    rw [hτ, hσ]
  · -- `⟨xstar, ystar⟩ ⊑ F.fixElement`.
    set fp := (paired τ σ).fixElement with hfp
    set a := fp.fst with ha
    set b := fp.snd with hb
    -- `τ(a, b) = a` and `σ(a, b) = b` (decompose the fixed point of `F`).
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
    -- `!x.τ(x, b) ⊑ a` since `τ(a, b) = a`.
    have hxfix_le : (secFixX τ).toElementMap b ≤ a := by
      rw [secFixX_apply]
      apply fixElement_le_of_toElementMap_le
      rw [sectionX_apply]
      exact le_of_eq hτa
    -- `outerOp(b) = σ(!x.τ(x,b), b) ⊑ σ(a, b) = b`.
    have houter_le : (outerOp τ σ).toElementMap b ≤ b := by
      rw [outerOp_apply]
      calc σ.toElementMap (pair ((secFixX τ).toElementMap b) b)
          ≤ σ.toElementMap (pair a b) :=
            σ.toElementMap_mono (pair_le_pair_iff.mpr ⟨hxfix_le, le_refl b⟩)
        _ = b := hσb
    -- so `ystar ⊑ b`, and `xstar = !x.τ(x, ystar) ⊑ !x.τ(x, b) ⊑ a`.
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
