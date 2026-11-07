module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SumProdRetracts

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Cond

universe u

theorem example_819 {α : Type u} {E : NeighborhoodSystem α}
    (hE : ∀ X, E.mem X → X.Nonempty) (hT : TD ⊴ E) (hArrow : funSpace E E ⊴ E) :
    sum E E hE hE ⊴ E ∧ prod E E ⊴ E :=
  exercise_8_19_assembly hE hT hArrow

