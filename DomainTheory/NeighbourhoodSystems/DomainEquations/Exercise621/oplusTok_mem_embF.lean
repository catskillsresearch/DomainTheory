/-ai
The false tag of a proper neighbourhood of the left system belongs to the coalesced sum.

It is the left-tag clause of the membership definition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplusTok

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem oplusTok_mem_embF {X : Set Str} (hX : D₀.mem X) (hXne : X ≠ D₀.master) :
    (oplusTok D₀ D₁ h₀ h₁).mem (embBit false X) := Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩)

end Exercise619

end DomainTheory.NeighbourhoodSystems
