/-ai
If both arguments of a pair embedding are contained in Gamma, the embedding is contained in Gamma.

A point of the embedding has its tail in one argument, hence in Gamma, and membership in Gamma depends only on the value.
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

theorem embPair_subset_Gamma {D : NeighborhoodSystem α} {P Q : Set (List Bool × α)}
    (hP : P ⊆ Gamma D) (hQ : Q ⊆ Gamma D) : embPair P Q ⊆ Gamma D := by
  rintro ⟨p, a⟩ (⟨p', -, hPmem⟩ | ⟨q', -, hQmem⟩)
  · have h := hP hPmem; exact h
  · have h := hQ hQmem; exact h

end Example61

end DomainTheory.NeighbourhoodSystems
