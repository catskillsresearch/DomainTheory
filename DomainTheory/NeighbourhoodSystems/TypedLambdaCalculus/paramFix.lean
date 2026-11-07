module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.fixMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

def pfix (τ : ApproximableMap (prod V V) V) : ApproximableMap V V :=
  (fixMap V).comp (curry τ)

def recOp (τ : ApproximableMap (prod V V) V) : ApproximableMap (funSpace V V) (funSpace V V) :=
  curry (τ.comp (paired (proj₁ (funSpace V V) V) (evalMap V V)))

def section₂ (τ : ApproximableMap (prod V V) V) (x : V.Element) : ApproximableMap V V :=
  toApproxMap ((curry τ).toElementMap x)

theorem pfix_apply (τ : ApproximableMap (prod V V) V) (x : V.Element) :
    (pfix τ).toElementMap x = (section₂ τ x).fixElement := by
  rw [pfix, toElementMap_comp, fixMap_toElementMap, section₂]

theorem recOp_apply (τ : ApproximableMap (prod V V) V) (φ : (funSpace V V).Element) (x : V.Element) :
    (toApproxMap ((recOp τ).toElementMap φ)).toElementMap x
      = τ.toElementMap (pair x ((toApproxMap φ).toElementMap x)) := by
  rw [recOp, toElementMap_curry_apply, toElementMap_comp, toElementMap_paired,
    toElementMap_proj₁, snd_pair, evalMap_apply]

theorem section₂_apply (τ : ApproximableMap (prod V V) V) (x y : V.Element) :
    (section₂ τ x).toElementMap y = τ.toElementMap (pair x y) := by
  rw [section₂, toElementMap_curry_apply]

theorem pfix_isFixed (τ : ApproximableMap (prod V V) V) (x : V.Element) :
    τ.toElementMap (pair x ((pfix τ).toElementMap x)) = (pfix τ).toElementMap x := by
  rw [pfix_apply, ← section₂_apply, toElementMap_fixElement]

/-- Parametric least fixed point equals the least fixed point of the recursion operator. -/
theorem pfix_eq_fixElement_recOp (τ : ApproximableMap (prod V V) V) :
    pfix τ = toApproxMap (recOp τ).fixElement := by
  set g₀ := (recOp τ).fixElement with hg₀
  set G := toApproxMap g₀ with hG
  have hG_fixed : ∀ x, G.toElementMap x = τ.toElementMap (pair x (G.toElementMap x)) := by
    intro x
    have hfix : (recOp τ).toElementMap g₀ = g₀ := toElementMap_fixElement (recOp τ)
    have := recOp_apply τ g₀ x
    rw [hfix] at this
    rw [hG]; exact this
  apply le_antisymm
  · rw [le_iff_toElementMap_le]
    intro x
    rw [pfix_apply]
    apply fixElement_le_of_toElementMap_le
    rw [section₂_apply]
    exact le_of_eq (hG_fixed x).symm
  · have hpre : (recOp τ).toElementMap (toFilter (pfix τ)) ≤ toFilter (pfix τ) := by
      apply le_of_eq
      have hmap : toApproxMap ((recOp τ).toElementMap (toFilter (pfix τ))) = pfix τ := by
        apply ext_of_toElementMap
        intro x
        rw [recOp_apply]
        have hround : toApproxMap (toFilter (pfix τ)) = pfix τ := by
          have he := (funSpaceEquiv V V).apply_symm_apply (pfix τ)
          rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he
        rw [hround, pfix_isFixed]
      have h1 : toFilter (toApproxMap ((recOp τ).toElementMap (toFilter (pfix τ)))) =
          toFilter (pfix τ) := by rw [hmap]
      have hround2 : toFilter (toApproxMap ((recOp τ).toElementMap (toFilter (pfix τ)))) =
          (recOp τ).toElementMap (toFilter (pfix τ)) := by
        have he := (funSpaceEquiv V V).symm_apply_apply ((recOp τ).toElementMap (toFilter (pfix τ)))
        rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he
      rw [hround2] at h1
      exact h1
    have hle : g₀ ≤ toFilter (pfix τ) := fixElement_le_of_toElementMap_le (recOp τ) hpre
    have := (funSpaceEquiv V V).monotone hle
    rw [funSpaceEquiv_apply, funSpaceEquiv_apply] at this
    have hround : toApproxMap (toFilter (pfix τ)) = pfix τ := by
      have he := (funSpaceEquiv V V).apply_symm_apply (pfix τ)
      rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he
    rw [hG, ← hround]
    exact this

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
