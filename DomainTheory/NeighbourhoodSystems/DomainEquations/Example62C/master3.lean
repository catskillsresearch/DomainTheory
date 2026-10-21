/-ai
The master neighbourhood of the three-way sum of V₀, V₁, and V₂ is the set obtained by inserting the basepoint into the union of the tagged left copy of the master of V₀, the tagged middle copy of the master of V₁, and the tagged right copy of the master of V₂.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t2_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_not_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_not_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_not_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1_not_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t2_not_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0_not_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t2_not_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0_not_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1_not_mem_j2

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

variable {α β γ : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)

/-- The master neighbourhood of the three-way sum: `{Λ} ∪ 0Δ₀ ∪ 1Δ₁ ∪ 2Δ₂`. -/
def master3 : Set (Option (α ⊕ β ⊕ γ)) :=
  insert none (j0 V₀.master ∪ j1 V₁.master ∪ j2 V₂.master)

end DomainTheory.NeighbourhoodSystems
