module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.prodIso

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- Scott's Exercise 3.15: product is commutative, congruent, and associative up to isomorphism. -/
theorem example_315 :
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β},
      prod V₀ V₁ ≅ᴰ prod V₁ V₀) ∧
    (∀ {α β α' β' : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'},
      V₀ ≅ᴰ V₀' → V₁ ≅ᴰ V₁' → prod V₀ V₁ ≅ᴰ prod V₀' V₁') ∧
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ},
      prod V₀ (prod V₁ V₂) ≅ᴰ prod (prod V₀ V₁) V₂) :=
  ⟨@prod_comm_isomorphic, @Isomorphic.prod, @prod_assoc_isomorphic⟩

