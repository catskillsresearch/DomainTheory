module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.MemS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embR
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS_mem_inj₁

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

theorem embZero_ne_embPair {X : Set α} (hX : D.mem X) (P Q : Set (List Bool × α)) :
    embZero X ≠ embPair P Q := by
  intro h
  obtain ⟨a, ha⟩ := hD X hX
  have hmem : (([], a) : List Bool × α) ∈ embPair P Q := h ▸ (⟨rfl, ha⟩ : ([], a) ∈ embZero X)
  rcases hmem with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
  · simp at hp'
  · simp at hq'

end Equation

end Example61

end DomainTheory.NeighbourhoodSystems
