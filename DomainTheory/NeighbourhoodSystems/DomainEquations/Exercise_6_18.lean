module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.iterProdInitial
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem_6_14

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.SmashProduct
open DomainTheory.NeighbourhoodSystems.IterProdInitial
/-- Scott's Exercise 6.18: strictness is preserved by the product of two approximable maps. -/
theorem example_618 {α β α' β' : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {f₀ : ApproximableMap V₀ V₀'}
    {f₁ : ApproximableMap V₁ V₁'} :
    IsStrict f₀ → IsStrict f₁ → IsStrict (prodMap f₀ f₁) :=
  isStrict_prodMap
