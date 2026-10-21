/-ai
Every neighbourhood of the three-way sum of the unit system with two copies of C is nonempty.

The four shapes are examined. The master contains the basepoint. A left copy is nonempty because its unit neighbourhood is nonempty. A middle copy and a right copy are nonempty because their neighbourhoods of C are nonempty.
ai-/
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j0_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j1_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j2_nonempty
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

theorem sum3_mem_nonempty {W : Set (Option (Unit ⊕ Str ⊕ Str))} (h : CC.mem W) : W.Nonempty := by
  rcases h with rfl | ⟨U, hU, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩
  · exact ⟨none, none_mem_master3⟩
  · exact j0_nonempty (unitSys_nonempty U hU)
  · exact j1_nonempty (C_nonempty Y hY)
  · exact j2_nonempty (C_nonempty Z hZ)

end Example62C

end DomainTheory.NeighbourhoodSystems
