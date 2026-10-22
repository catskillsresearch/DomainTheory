module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftBot

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

@[simp] theorem mem_liftBot {W : Set Str} : (liftBot D hD).mem W ↔ W = liftTokMaster D := Iff.rfl

end Exercise619

end DomainTheory.NeighbourhoodSystems
