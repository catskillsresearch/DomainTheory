/-ai
A tagged point lies in the zero-embedding of a set X exactly when its boolean list is empty and the element lies in X.

The equivalence is the definition of the zero-embedding.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.MemS

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

@[simp] theorem mem_embZero {X : Set α} {p : List Bool} {a : α} :
    (p, a) ∈ embZero X ↔ p = [] ∧ a ∈ X := Iff.rfl

end Example61

end DomainTheory.NeighbourhoodSystems
