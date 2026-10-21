/-ai
The step set of an input and an output is the set of approximable maps that relate that input to that output.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.BasicInst3

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Scott's step set `[X, Y] = {f ∣ X f Y}`. -/
def step (X : Set α) (Y : Set β) : Set (ApproximableMap V₀ V₁) := {f | f.rel X Y}

end DomainTheory.NeighbourhoodSystems
