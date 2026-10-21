/-ai
The sum of E with itself is a retract of the product of the three-point domain with the product of E with itself.

The tagging embedding and the conditional sum form a projection pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.condSum_comp_sumToProdT
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.sumToProdT_comp_condSum_le

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u








section Sum

variable {α : Type u} {E : NeighborhoodSystem α} (hE : ∀ X, E.mem X → X.Nonempty)


/-- **`E + E ⊴ T × (E × E)`.** -/
theorem sum_trianglelefteq_prodT : sum E E hE hE ⊴ prod TD (prod E E) :=
  trianglelefteq_of_projectionPair (sumToProdT hE) (condSum E E hE hE) (condSum_comp_sumToProdT hE)
    (sumToProdT_comp_condSum_le hE)

end Sum
end DomainTheory.NeighbourhoodSystems
