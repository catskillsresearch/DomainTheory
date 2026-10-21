/-ai
Equal pair embeddings have equal left arguments and equal right arguments.

Equality gives mutual inclusions. The subset characterization of the pair embedding turns each inclusion into inclusions of both components, and antisymmetry equates the components.
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_subset

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embPair_injective {P Q P' Q' : Set (List Bool × α)}
    (h : embPair P Q = embPair P' Q') : P = P' ∧ Q = Q' := by
  obtain ⟨hP, hQ⟩ := embPair_subset.mp h.subset
  obtain ⟨hP', hQ'⟩ := embPair_subset.mp h.symm.subset
  exact ⟨Set.Subset.antisymm hP hP', Set.Subset.antisymm hQ hQ'⟩

end Example61

end DomainTheory.NeighbourhoodSystems
