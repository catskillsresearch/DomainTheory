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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j2_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_mem_master3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.unitSys_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.C_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.CC

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

variable {α β γ : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)

variable {V₀ V₁ V₂}

namespace Example62C

theorem sum3_mem_j2_inv {Y : Set Str} (h : CC.mem (j2 Y)) : C.mem Y := by
  rcases h with h0 | ⟨U, hU, heq⟩ | ⟨Z, hZ, heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j2
  · obtain ⟨a, ha⟩ := unitSys_nonempty U hU; exact absurd (heq ▸ (t0_mem_j0.mpr ha)) t0_not_mem_j2
  · obtain ⟨c, hc⟩ := C_nonempty Z hZ; exact absurd (heq ▸ (t1_mem_j1.mpr hc)) t1_not_mem_j2
  · rw [j2_injective heq]; exact hY'

end Example62C

end DomainTheory.NeighbourhoodSystems
