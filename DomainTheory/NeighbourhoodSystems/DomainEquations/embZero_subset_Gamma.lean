/-ai
The zero embedding of a neighbourhood is contained in Gamma.

A point of the zero embedding has its value in the neighbourhood, and every point of a neighbourhood lies in the master, which is membership in Gamma.
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

theorem embZero_subset_Gamma {D : NeighborhoodSystem α} {X : Set α} (hX : D.mem X) :
    embZero X ⊆ Gamma D := by
  rintro ⟨p, a⟩ ⟨-, ha⟩; exact D.sub_master hX ha

end Example61

end DomainTheory.NeighbourhoodSystems
