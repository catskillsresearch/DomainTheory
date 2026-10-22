module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j0

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

variable {α β γ : Type*}

@[simp] theorem t0_mem_j0 {X : Set α} {a : α} : (t0 a : Option (α ⊕ β ⊕ γ)) ∈ j0 X ↔ a ∈ X := by
  constructor
  · rintro ⟨a', heq, ha'⟩; simp only [t0, Option.some.injEq, Sum.inl.injEq] at heq; exact heq ▸ ha'
  · intro ha; exact ⟨a, rfl, ha⟩

end DomainTheory.NeighbourhoodSystems
