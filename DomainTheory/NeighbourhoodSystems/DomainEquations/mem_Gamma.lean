/-ai
A pair of a boolean list and an element lies in the master of D-sharp exactly when the element lies in the master of D.

The equivalence is the definition of that master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.MemS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embR
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embPair

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

@[simp] theorem mem_Gamma {D : NeighborhoodSystem α} {p : List Bool} {a : α} :
    (p, a) ∈ Gamma D ↔ a ∈ D.master := Iff.rfl

end Example61

end DomainTheory.NeighbourhoodSystems
