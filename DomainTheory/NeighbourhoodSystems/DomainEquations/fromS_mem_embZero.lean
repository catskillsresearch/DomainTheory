/-ai
An element of the sum system contains the zero-injection of a neighbourhood X of D if and only if its image under fromS contains the zero-embedding of X.

If that image contains the zero-embedding, the three clauses of fromS apply. The master clause is impossible because a zero-embedding is not the master, and the pair clause is impossible because a zero-embedding is not a pair embedding. The remaining clause is a zero-copy, and injectivity of the zero-embedding recovers membership of the zero-injection. Conversely, membership of the zero-injection is exactly that zero-copy clause.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.MemS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embR
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumSys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.fromS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_ne_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_ne_embPair

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

@[simp] theorem fromS_mem_embZero {s : (sumSys D hD).Element} {X : Set α} (hX : D.mem X) :
    (fromS D hD s).mem (embZero X) ↔ s.mem (inj₀ X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨P, Q, hP, hQ, heq, hs⟩)
    · exact absurd h0 (embZero_ne_Gamma D hD X)
    · rwa [embZero_injective heq]
    · exact absurd heq (embZero_ne_embPair D hD hX P Q)
  · intro hs; exact Or.inr (Or.inl ⟨X, hX, rfl, hs⟩)

end Equation

end Example61

end DomainTheory.NeighbourhoodSystems
