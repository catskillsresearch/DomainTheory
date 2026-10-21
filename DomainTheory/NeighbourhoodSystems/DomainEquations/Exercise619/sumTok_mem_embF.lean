/-ai
If X is a neighbourhood of the first system, its false-tagged copy is a neighbourhood of the concrete sum.

It is the left-copy clause of the membership definition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTok

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem sumTok_mem_embF {X : Set Str} (hX : D₀.mem X) :
    (sumTok D₀ D₁ h₀ h₁).mem (embBit false X) := Or.inr (Or.inl ⟨X, hX, rfl⟩)

end Exercise619

end DomainTheory.NeighbourhoodSystems
