/-ai
If the left argument of a pair embedding is nonempty, the embedding is nonempty.

A point of the left argument, with true placed at the head of its path, lies in the left copy of the embedding.
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

theorem embPair_nonempty {P Q : Set (List Bool × α)} (hP : P.Nonempty) :
    (embPair P Q).Nonempty := by
  obtain ⟨⟨p', a⟩, hP⟩ := hP; exact ⟨(true :: p', a), Or.inl ⟨p', rfl, hP⟩⟩

end Example61

end DomainTheory.NeighbourhoodSystems
