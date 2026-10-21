/-ai
The master of the concrete token sum is a neighbourhood of that sum.

It is the master clause of the membership definition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}











variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem sumTok_mem_master : (sumTok D₀ D₁ h₀ h₁).mem (sumTokMaster D₀ D₁) := Or.inl rfl

end Exercise619
end DomainTheory.NeighbourhoodSystems
