/-ai
Any neighbourhood system B is a retract of the function space from A to B, by the constant-function embedding and evaluation at bottom.

Those two maps form a projection pair: evaluation after the embedding is the identity, and the embedding after evaluation lies below the identity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.evalBotMap_comp_constFunMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.constFunMap_comp_evalBotMap_le

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u v


section FunSpace

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)


/-- **`B ⊴ funSpace A B`**, via `b ↦ (λ_. b)` / evaluation at `⊥`. -/
theorem trianglelefteq_funSpace_const : B ⊴ funSpace A B :=
  trianglelefteq_of_projectionPair (constFunMap A B) (evalBotMap A B)
    (evalBotMap_comp_constFunMap A B) (constFunMap_comp_evalBotMap_le A B)

end FunSpace
end DomainTheory.NeighbourhoodSystems
