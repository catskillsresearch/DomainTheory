module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.graphClosure

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem
open DomainTheory.NeighbourhoodSystems.GraphClosure
/-- Scott's Exercise 3.27: graphs of approximable maps are closed under directed unions. -/
theorem example_327 :
    ∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (𝒮 : Set (Set (Set α × Set β))),
      𝒮.Nonempty → 𝒮 ⊆ C V₀ V₁ → DirectedOn (· ⊆ ·) 𝒮 → ⋃₀ 𝒮 ∈ C V₀ V₁ :=
  @C_dir

