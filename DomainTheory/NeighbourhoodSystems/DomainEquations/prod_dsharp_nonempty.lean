module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.MemS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embR
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.memS_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- No neighbourhood of `D^§ × D^§` is empty (needed to form the sum `D + (D^§ × D^§)`). -/
theorem prod_dsharp_nonempty :
    ∀ V, (prod (Dsharp D hD) (Dsharp D hD)).mem V → V.Nonempty := by
  rintro V ⟨P, Q, hP, hQ, rfl⟩
  obtain ⟨t, ht⟩ := memS_nonempty hD hP
  exact ⟨Sum.inl t, mem_prodNbhd_inl.mpr ht⟩

end Equation

end Example61

end DomainTheory.NeighbourhoodSystems
