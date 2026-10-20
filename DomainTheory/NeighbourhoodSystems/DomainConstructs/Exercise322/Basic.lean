/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.FunctionSpace

@[expose] public section

/-!
# Exercise 3.22 (Scott 1981, PRG-19, §3) — composition is approximable

Scott asks for the approximable composition mapping

`comp : (𝒟₁ → 𝒟₂) × (𝒟₀ → 𝒟₁) → (𝒟₀ → 𝒟₂)`,  `comp(g, f) = g ∘ f`,

and suggests building it from `eval` and `curry`. We follow the hint: the uncurried form

`compApp : ((𝒟₁ → 𝒟₂) × (𝒟₀ → 𝒟₁)) × 𝒟₀ → 𝒟₂`,  `compApp(⟨⟨g, f⟩, x⟩) = g(f(x))`,

is assembled from the two evaluation maps and the projections/pairing of Definition 3.3, and then
`compMap = curry compApp` is the desired map. Theorem 3.12's `toElementMap_curry_apply` and 3.11's
`evalMap_apply` compute `comp(g, f) = g ∘ f` on elements (`toElementMap_compMap_apply`).

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- The uncurried composition map `((𝒟₁→𝒟₂) × (𝒟₀→𝒟₁)) × 𝒟₀ → 𝒟₂`, `⟨⟨g, f⟩, x⟩ ↦ g(f(x))`,
built from the inner evaluation `(𝒟₀→𝒟₁) × 𝒟₀ → 𝒟₁`, the outer evaluation `(𝒟₁→𝒟₂) × 𝒟₁ → 𝒟₂`,
and the product projections/pairing (Definition 3.3). -/
def compApp (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
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

/-- **Exercise 3.22 (Scott 1981, PRG-19).** The composition mapping
`comp : (𝒟₁ → 𝒟₂) × (𝒟₀ → 𝒟₁) → (𝒟₀ → 𝒟₂)`, `comp = curry(compApp)`. -/
def compMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) (funSpace V₀ V₂) :=
  curry (compApp V₀ V₁ V₂)
end DomainTheory.Neighborhood
