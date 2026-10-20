module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise322.compApp
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise322.compMap

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

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


end DomainTheory.NeighbourhoodSystems
