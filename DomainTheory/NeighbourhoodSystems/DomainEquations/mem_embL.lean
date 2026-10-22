module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.MemS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embZero

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

@[simp] theorem mem_embL {P : Set (List Bool × α)} {p : List Bool} {a : α} :
    (p, a) ∈ embL P ↔ ∃ p', p = true :: p' ∧ (p', a) ∈ P := Iff.rfl

end Example61

end DomainTheory.NeighbourhoodSystems
