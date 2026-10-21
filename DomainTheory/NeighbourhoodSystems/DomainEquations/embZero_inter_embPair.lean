/-ai
A zero embedding is disjoint from every pair embedding.

A common point would have empty path from the zero embedding and a cons path from one of the two tagged copies of the pair embedding.
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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embZero_inter_embPair (X : Set α) (P Q : Set (List Bool × α)) :
    embZero X ∩ embPair P Q = ∅ := by
  ext ⟨p, a⟩
  simp only [Set.mem_inter_iff, mem_embZero, mem_embPair, Set.mem_empty_iff_false, iff_false,
    not_and, not_or]
  rintro ⟨rfl, -⟩
  exact ⟨by rintro ⟨p', hp', -⟩; exact absurd hp' (by simp), by rintro ⟨q', hq', -⟩; exact absurd hq' (by simp)⟩

end Example61

end DomainTheory.NeighbourhoodSystems
