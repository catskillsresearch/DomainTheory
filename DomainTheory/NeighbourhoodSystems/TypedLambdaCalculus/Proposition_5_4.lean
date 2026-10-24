module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_16

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
variable {α : Type*} {V : NeighborhoodSystem α}
namespace ApproximableMap
/- concordance: source L2799 PROPOSITION 5.4 fixed point under a parameter -/
/-- **Proposition 5.4 (Scott 1981, PRG-19).** `λx. !y. τ(x, y) = !g. λx. τ(x, g(x))`. -/
theorem pfix_eq_fixElement_recOp (τ : ApproximableMap (prod V V) V) :
    pfix τ = toApproxMap (recOp τ).fixElement := by
  set g₀ := (recOp τ).fixElement with hg₀
  set G := toApproxMap g₀ with hG
  -- `G(x) = τ(x, G(x))`: `g₀` is a fixed point of `recOp τ`.
  have hG_fixed : ∀ x, G.toElementMap x = τ.toElementMap (pair x (G.toElementMap x)) := by
    intro x
    have hfix : (recOp τ).toElementMap g₀ = g₀ := toElementMap_fixElement (recOp τ)
    have := recOp_apply τ g₀ x
    rw [hfix] at this
    rw [hG]; exact this
  apply le_antisymm
  · -- `pfix τ ⊑ G`: `pfix τ (x)` is the least fixed point of the section, `G(x)` is some fixed point.
    rw [le_iff_toElementMap_le]
    intro x
    rw [pfix_apply]
    apply fixElement_le_of_toElementMap_le
    rw [section₂_apply]
    exact le_of_eq (hG_fixed x).symm
  · -- `G ⊑ pfix τ`: `toFilter (pfix τ)` is a fixed point of `recOp τ`, so `g₀ ⊑ toFilter (pfix τ)`.
    have hpre : (recOp τ).toElementMap (toFilter (pfix τ)) ≤ toFilter (pfix τ) := by
      apply le_of_eq
      have hmap : toApproxMap ((recOp τ).toElementMap (toFilter (pfix τ))) = pfix τ := by
        apply ext_of_toElementMap
        intro x
        rw [recOp_apply]
        have hround : toApproxMap (toFilter (pfix τ)) = pfix τ := by
          have he := (funSpaceEquiv V V).apply_symm_apply (pfix τ)
          rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he
        rw [hround, pfix_isFixed]
      -- transport `hmap` through the iso `toApproxMap`/`toFilter`.
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
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

end
end DomainTheory.NeighbourhoodSystems
end
