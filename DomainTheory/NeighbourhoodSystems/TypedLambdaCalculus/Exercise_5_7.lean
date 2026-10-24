module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

section
/- concordance: source L3005 EXERCISE 5.7 currying the lambda notation -/
/- concordance: source L3003 EXERCISES — Lecture V exercises -/
-- Exercise507/curry₃.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise507

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ} {V₃ : NeighborhoodSystem δ}

/-- **Three-variable abstraction** `λx, y, z. τ`, via nested currying on `(D₀ × D₁) × D₂ → D₃`.
Each `curry` strips one variable, so a function of `n` variables is reached by `n - 1` curryings —
single-variable binders all the way down. -/
def curry₃ (g : ApproximableMap (prod (prod V₀ V₁) V₂) V₃) :
    ApproximableMap V₀ (funSpace V₁ (funSpace V₂ V₃)) :=
  curry (curry g)

end DomainTheory.NeighbourhoodSystems.Exercise507
end

section
namespace DomainTheory.NeighbourhoodSystems.Exercise507
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The combinator `σ(x, y)` (apply `σ : D₀ × D₁ → D₂` to two arguments) is expressed through the
*one-variable* curried form: `σ(⟨x, y⟩) = (curry σ)(x)(y)`. The right-hand side uses only
single-variable application. -/
theorem app_two_args (σ : ApproximableMap (prod V₀ V₁) V₂) (x : V₀.Element) (y : V₁.Element) :
    σ.toElementMap (pair x y) =
      (toApproxMap ((curry σ).toElementMap x)).toElementMap y := by
  rw [toElementMap_curry_apply]

/-- The defining equation of `curry₃`: `(λx, y, z. g)(x)(y)(z) = g⟨⟨x, y⟩, z⟩`. -/
theorem curry₃_apply (g : ApproximableMap (prod (prod V₀ V₁) V₂) V₃)
    (x : V₀.Element) (y : V₁.Element) (z : V₂.Element) :
    (toApproxMap ((toApproxMap ((curry₃ g).toElementMap x)).toElementMap y)).toElementMap z =
      g.toElementMap (pair (pair x y) z) := by
  rw [curry₃, toElementMap_curry_apply, toElementMap_curry_apply]

/-- **Two-variable abstraction.** `λx, y. τ` is `curry`, characterised by `(curry g)(x)(y) = g⟨x, y⟩`.
It binds one variable `x` and returns the one-variable function `λy. g⟨x, y⟩`. -/
theorem lam_two_vars (g : ApproximableMap (prod V₀ V₁) V₂) (x : V₀.Element) (y : V₁.Element) :
    (toApproxMap ((curry g).toElementMap x)).toElementMap y = g.toElementMap (pair x y) :=
  toElementMap_curry_apply g x y

/-- **Surjective pairing.** Every element `z : D₀ × D₁` is recovered from its projections:
`⟨p₀(z), p₁(z)⟩ = z`. This is what makes `p₀`, `p₁`, `pair` enough to encode the product. -/
theorem surjective_pairing (z : (prod V₀ V₁).Element) :
    pair ((proj₀ V₀ V₁).toElementMap z) ((proj₁ V₀ V₁).toElementMap z) = z := by
  rw [toElementMap_proj₀, toElementMap_proj₁, pair_fst_snd]

/-- **One-argument-at-a-time application.** For `h : D₀ → (D₁ → D₂)`, applying the uncurried map to
a `pair` is the same as applying `h` to `x` and then to `y`:
`(uncurry h)(⟨x, y⟩) = h(x)(y)`. -/
theorem uncurry_apply (h : ApproximableMap V₀ (funSpace V₁ V₂))
    (x : V₀.Element) (y : V₁.Element) :
    (uncurry h).toElementMap (pair x y) =
      (toApproxMap (h.toElementMap x)).toElementMap y := by
  rw [uncurry_eq, toElementMap_comp, toElementMap_paired, toElementMap_comp,
    toElementMap_proj₀, toElementMap_proj₁, fst_pair, snd_pair, evalMap_apply]

/-- The two encodings are mutually inverse: uncurrying the two-variable abstraction returns the
original two-variable function. -/
theorem uncurry_lam_two_vars (g : ApproximableMap (prod V₀ V₁) V₂) : uncurry (curry g) = g :=
  uncurry_curry g

end

section
set_option linter.unusedVariables false

theorem example_507.{u_1, u_2, u_5} : ∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {α_1 : Type u_5}
  {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
  (g :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) α_1 (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
      V₂),
  @Eq
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) α_1
      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
    (@DomainTheory.NeighbourhoodSystems.uncurry α β α_1 V₀ V₁ V₂
      (@DomainTheory.NeighbourhoodSystems.curry α β α_1 V₀ V₁ V₂ g))
    g :=
  @DomainTheory.NeighbourhoodSystems.Exercise507.uncurry_lam_two_vars
end

end DomainTheory.NeighbourhoodSystems.Exercise507
end
