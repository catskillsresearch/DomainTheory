module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.MemS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embR

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

@[simp] theorem mem_embPair {P Q : Set (List Bool × α)} {p : List Bool} {a : α} :
    (p, a) ∈ embPair P Q ↔
      (∃ p', p = true :: p' ∧ (p', a) ∈ P) ∨ (∃ q', p = false :: q' ∧ (q', a) ∈ Q) := Iff.rfl

end Example61

end DomainTheory.NeighbourhoodSystems
