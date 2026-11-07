module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.unarySeq
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.fixMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ofIso
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.prodEquiv
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Lemma_3_6


@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

def P₀ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : ApproximableMap (prod V₀ V₁) V₀ :=
  proj₀ V₀ V₁

@[simp] theorem P₀_apply (x : V₀.Element) (y : V₁.Element) :
    (P₀ V₀ V₁).toElementMap (pair x y) = x := by
  rw [P₀, toElementMap_proj₀, fst_pair]

def P₁ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : ApproximableMap (prod V₀ V₁) V₁ :=
  proj₁ V₀ V₁

@[simp] theorem P₁_apply (x : V₀.Element) (y : V₁.Element) :
    (P₁ V₀ V₁).toElementMap (pair x y) = y := by
  rw [P₁, toElementMap_proj₁, snd_pair]

def diagC (V : NeighborhoodSystem α) : ApproximableMap V (prod V V) := paired (idMap V) (idMap V)

@[simp] theorem diagC_apply (x : V.Element) : (diagC V).toElementMap x = pair x x := by
  rw [diagC, toElementMap_paired, toElementMap_idMap]

def pairC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap V₀ (funSpace V₁ (prod V₀ V₁)) := curry (idMap (prod V₀ V₁))

def swapC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (prod V₀ V₁) (prod V₁ V₀) := paired (proj₁ V₀ V₁) (proj₀ V₀ V₁)

@[simp] theorem swapC_apply (x : V₀.Element) (y : V₁.Element) :
    (swapC V₀ V₁).toElementMap (pair x y) = pair y x := by
  rw [swapC, toElementMap_paired, toElementMap_proj₁, toElementMap_proj₀, snd_pair, fst_pair]

def compMapTbl (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀) V₂ :=
  (evalMap V₁ V₂).comp
    (paired
      ((proj₀ (funSpace V₁ V₂) (funSpace V₀ V₁)).comp
        (proj₀ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))
      ((evalMap V₀ V₁).comp
        (paired
          ((proj₁ (funSpace V₁ V₂) (funSpace V₀ V₁)).comp
            (proj₀ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))
          (proj₁ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))))

def compC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) (funSpace V₀ V₂) :=
  curry (compMapTbl V₀ V₁ V₂)

def constC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap V₁ (funSpace V₀ V₁) := curry (proj₀ V₁ V₀)

def curryIso (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    (funSpace (prod V₀ V₁) V₂).Element ≃o (funSpace V₀ (funSpace V₁ V₂)).Element :=
  (funSpaceEquiv (prod V₀ V₁) V₂).trans
    ((curryEquiv V₀ V₁ V₂).trans (funSpaceEquiv V₀ (funSpace V₁ V₂)).symm)

def curryC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (funSpace (prod V₀ V₁) V₂) (funSpace V₀ (funSpace V₁ V₂)) :=
  ofIso (curryIso V₀ V₁ V₂)

def evalC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (prod (funSpace V₀ V₁) V₀) V₁ := evalMap V₀ V₁

def fixC (V : NeighborhoodSystem α) : ApproximableMap (funSpace V V) V := fixMap V

def funpairMapTbl (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (prod (funSpace V₂ V₀) (funSpace V₂ V₁)) V₂) (prod V₀ V₁) :=
  paired
    ((evalMap V₂ V₀).comp
      (paired
        ((proj₀ (funSpace V₂ V₀) (funSpace V₂ V₁)).comp
          (proj₀ (prod (funSpace V₂ V₀) (funSpace V₂ V₁)) V₂))
        (proj₁ (prod (funSpace V₂ V₀) (funSpace V₂ V₁)) V₂)))
    ((evalMap V₂ V₁).comp
      (paired
        ((proj₁ (funSpace V₂ V₀) (funSpace V₂ V₁)).comp
          (proj₀ (prod (funSpace V₂ V₀) (funSpace V₂ V₁)) V₂))
        (proj₁ (prod (funSpace V₂ V₀) (funSpace V₂ V₁)) V₂)))

def funpairC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (funSpace V₂ V₀)
      (funSpace (funSpace V₂ V₁) (funSpace V₂ (prod V₀ V₁))) :=
  curry (curry (funpairMapTbl V₀ V₁ V₂))

end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem compC_apply (φ : (funSpace V₁ V₂).Element) (ψ : (funSpace V₀ V₁).Element) (x : V₀.Element) :
    (toApproxMap ((compC V₀ V₁ V₂).toElementMap (pair φ ψ))).toElementMap x
      = (toApproxMap φ).toElementMap ((toApproxMap ψ).toElementMap x) := by
  rw [compC, toElementMap_curry_apply, compMapTbl]
  simp only [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

theorem compC_eq_comp (φ : (funSpace V₁ V₂).Element) (ψ : (funSpace V₀ V₁).Element) :
    toApproxMap ((compC V₀ V₁ V₂).toElementMap (pair φ ψ)) = (toApproxMap φ).comp (toApproxMap ψ) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, compC_apply]

theorem constC_apply (k : V₁.Element) (x : V₀.Element) :
    (toApproxMap ((constC V₀ V₁).toElementMap k)).toElementMap x = k := by
  rw [constC, toElementMap_curry_apply, toElementMap_proj₀, fst_pair]

theorem constC_eq_constMap (k : V₁.Element) :
    toApproxMap ((constC V₀ V₁).toElementMap k) = constMap V₀ k := by
  apply ext_of_toElementMap
  intro x
  rw [constC_apply, toElementMap_constMap]

theorem curryC_toApproxMap (φ : (funSpace (prod V₀ V₁) V₂).Element) :
    toApproxMap ((curryC V₀ V₁ V₂).toElementMap φ) = curry (toApproxMap φ) := by
  rw [curryC, toElementMap_ofIso]
  show toApproxMap (toFilter (curry (toApproxMap φ))) = curry (toApproxMap φ)
  have he := (funSpaceEquiv V₀ (funSpace V₁ V₂)).apply_symm_apply (curry (toApproxMap φ))
  rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he

theorem curryC_apply (φ : (funSpace (prod V₀ V₁) V₂).Element) (x : V₀.Element) (y : V₁.Element) :
    (toApproxMap ((toApproxMap ((curryC V₀ V₁ V₂).toElementMap φ)).toElementMap x)).toElementMap y
      = (toApproxMap φ).toElementMap (pair x y) := by
  rw [curryC_toApproxMap, toElementMap_curry_apply]

theorem evalC_apply (φ : (funSpace V₀ V₁).Element) (x : V₀.Element) :
    (evalC V₀ V₁).toElementMap (pair φ x) = (toApproxMap φ).toElementMap x := by
  rw [evalC, evalMap_apply]

theorem fixC_apply (φ : (funSpace V V).Element) :
    (fixC V).toElementMap φ = (toApproxMap φ).fixElement := by
  rw [fixC, fixMap_toElementMap]

theorem fixC_fixed (φ : (funSpace V V).Element) :
    (toApproxMap φ).toElementMap ((fixC V).toElementMap φ) = (fixC V).toElementMap φ := by
  rw [fixC]; exact fixMap_fixed V φ

theorem funpairC_apply (φ : (funSpace V₂ V₀).Element) (ψ : (funSpace V₂ V₁).Element)
    (x : V₂.Element) :
    (toApproxMap ((toApproxMap ((funpairC V₀ V₁ V₂).toElementMap φ)).toElementMap ψ)).toElementMap x
      = pair ((toApproxMap φ).toElementMap x) ((toApproxMap ψ).toElementMap x) := by
  rw [funpairC, toElementMap_curry_apply, toElementMap_curry_apply, funpairMapTbl]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

theorem funpairC_eq_paired (φ : (funSpace V₂ V₀).Element) (ψ : (funSpace V₂ V₁).Element) :
    toApproxMap ((toApproxMap ((funpairC V₀ V₁ V₂).toElementMap φ)).toElementMap ψ)
      = paired (toApproxMap φ) (toApproxMap ψ) := by
  apply ext_of_toElementMap
  intro x
  rw [funpairC_apply, toElementMap_paired]

theorem pairC_apply (x : V₀.Element) (y : V₁.Element) :
    (toApproxMap ((pairC V₀ V₁).toElementMap x)).toElementMap y = pair x y := by
  rw [pairC, toElementMap_curry_apply, toElementMap_idMap]

end

section
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
end
end DomainTheory.NeighbourhoodSystems
end
