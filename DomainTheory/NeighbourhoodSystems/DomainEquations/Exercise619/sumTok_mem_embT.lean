/-ai
If Y is a neighbourhood of the second system, its true-tagged copy is a neighbourhood of the concrete sum.

It is the right-copy clause of the membership definition.
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

theorem sumTok_mem_embT {Y : Set Str} (hY : D₁.mem Y) :
    (sumTok D₀ D₁ h₀ h₁).mem (embBit true Y) := Or.inr (Or.inr ⟨Y, hY, rfl⟩)

end Exercise619

end DomainTheory.NeighbourhoodSystems
