/-ai
A set of path-token pairs is a neighbourhood of the tree algebra if and only if it belongs to the inductive family of tree-algebra neighbourhoods.

The two sides are identical by the definition of the tree algebra.
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

@[simp] theorem Dsharp_mem {D : NeighborhoodSystem α} {hD : ∀ X, D.mem X → X.Nonempty}
    {W : Set (List Bool × α)} : (Dsharp D hD).mem W ↔ MemS D W := Iff.rfl

end Example61

end DomainTheory.NeighbourhoodSystems
