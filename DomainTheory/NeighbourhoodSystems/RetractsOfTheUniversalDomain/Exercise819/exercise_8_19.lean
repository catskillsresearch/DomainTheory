/-ai
If every neighbourhood of E is nonempty, the truth-value domain embeds in E, and the function space of E with itself embeds in E, then both the sum of E with itself and the product of E with itself embed in E.

The sum embedding is the sum comparison under these hypotheses, and the product embedding is the product comparison under these hypotheses.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.prod_trianglelefteq_of
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.sum_trianglelefteq_of

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u


/-- **Exercise 8.19.** If `T ⊴ E` and `E → E ⊴ E`, then `E + E ⊴ E` and `E × E ⊴ E`. -/
theorem exercise_8_19 {α : Type u} {E : NeighborhoodSystem α}
    (hE : ∀ X, E.mem X → X.Nonempty) (hT : TD ⊴ E) (hArrow : funSpace E E ⊴ E) :
    sum E E hE hE ⊴ E ∧ prod E E ⊴ E :=
  ⟨sum_trianglelefteq_of hE hT hArrow, prod_trianglelefteq_of hT hArrow⟩

end DomainTheory.NeighbourhoodSystems
