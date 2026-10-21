/-ai
One zero embedding is contained in another exactly when the underlying set is contained in the other.

From a containment, a point of the smaller set paired with the empty path lies in the larger embedding, so the point lies in the larger set. From an inclusion of sets, a point of the smaller embedding has empty path and a value in the smaller set, hence in the larger set.
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

theorem embZero_subset {X X' : Set α} : embZero X ⊆ embZero X' ↔ X ⊆ X' := by
  constructor
  · intro h a ha
    have : (([], a) : List Bool × α) ∈ embZero X' := h ⟨rfl, ha⟩
    exact this.2
  · intro h t ht; exact ⟨ht.1, h ht.2⟩

end Example61

end DomainTheory.NeighbourhoodSystems
