module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.master3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_mem_master3

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

variable {α β γ : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)

variable {V₀ V₁ V₂}

theorem j2_subset_master3 {Z : Set γ} (hZ : V₂.mem Z) :
    (j2 Z : Set (Option (α ⊕ β ⊕ γ))) ⊆ master3 V₀ V₁ V₂ := by
  rintro w ⟨c, rfl, hc⟩
  exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_union_right _ (t2_mem_j2.mpr (V₂.sub_master hZ hc))))

end DomainTheory.NeighbourhoodSystems
