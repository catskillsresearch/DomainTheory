module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_mem_master3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.memC_cases
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.toCC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.toCC_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.toCC_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.toCC_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.fromCC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.fromCC_mem_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.fromCC_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.fromCC_mem_embT

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

variable {α β γ : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)

variable {V₀ V₁ V₂}

namespace Example62C

theorem fromCC_toCC (x : C.Element) : fromCC (toCC x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hs⟩ | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact x.master_mem
    · exact toCC_mem_j0.mp hs
    · exact (toCC_mem_j1 hX).mp hs
    · exact (toCC_mem_j2 hY).mp hs
  · intro hW
    rcases memC_cases (x.sub hW) with rfl | rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, toCC_mem_j0.mpr hW⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, (toCC_mem_j1 hX).mpr hW⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, (toCC_mem_j2 hY).mpr hW⟩))

end Example62C

end DomainTheory.NeighbourhoodSystems
