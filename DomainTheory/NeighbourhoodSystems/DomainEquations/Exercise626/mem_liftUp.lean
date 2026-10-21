/-ai
A set belongs to the lift of an element x if and only if it is the lift master or the false tag of a neighbourhood of x.

The equivalence is definitional.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftUp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftBot

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

@[simp] theorem mem_liftUp {x : D.Element} {W : Set Str} :
    (liftUp (hD := hD) x).mem W ↔ W = liftTokMaster D ∨ ∃ X, x.mem X ∧ W = embBit false X := Iff.rfl

end Exercise619

end DomainTheory.NeighbourhoodSystems
