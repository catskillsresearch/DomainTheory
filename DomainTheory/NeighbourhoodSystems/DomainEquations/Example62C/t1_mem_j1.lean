/-ai
The middle tag of b lies in the tagged middle copy of Y if and only if b lies in Y.

From a membership witness, simplification of the option, right-sum, and left-sum injections identifies the underlying element with b, and membership transports. Conversely, b itself is a witness that its middle tag lies in the copy.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0_mem_j0

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

variable {α β γ : Type*}

@[simp] theorem t1_mem_j1 {Y : Set β} {b : β} : (t1 b : Option (α ⊕ β ⊕ γ)) ∈ j1 Y ↔ b ∈ Y := by
  constructor
  · rintro ⟨b', heq, hb'⟩
    simp only [t1, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq] at heq; exact heq ▸ hb'
  · intro hb; exact ⟨b, rfl, hb⟩

end DomainTheory.NeighbourhoodSystems
