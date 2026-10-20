module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

@[simp] theorem relSystem_mem (a : V.Element) {X : Set α} :
    (relSystem a).mem X ↔ a.mem X := Iff.rfl

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
