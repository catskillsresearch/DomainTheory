/-ai
If the tagged middle copy of X is a neighbourhood of the three-way sum of the unit system with two copies of C, then X is a neighbourhood of C.

The four shapes of such a neighbourhood are examined. The master would place the basepoint in the middle copy. A left copy would place a point of its nonempty unit neighbourhood, read through the left tag, in the middle copy. A middle copy equals the given copy, so injectivity identifies X with a neighbourhood of C. A right copy would place a point of its nonempty neighbourhood of C, read through the right tag, in the middle copy. Each mismatched token is excluded by the corresponding non-membership lemma.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j1
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j1_injective
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

theorem sum3_mem_j1_inv {X : Set Str} (h : CC.mem (j1 X)) : C.mem X := by
  rcases h with h0 | ⟨U, hU, heq⟩ | ⟨Y, hY, heq⟩ | ⟨Z, hZ, heq⟩
  · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j1
  · obtain ⟨a, ha⟩ := unitSys_nonempty U hU; exact absurd (heq ▸ (t0_mem_j0.mpr ha)) t0_not_mem_j1
  · rw [j1_injective heq]; exact hY
  · obtain ⟨c, hc⟩ := C_nonempty Z hZ; exact absurd (heq ▸ (t2_mem_j2.mpr hc)) t2_not_mem_j1

end Example62C

end DomainTheory.NeighbourhoodSystems
