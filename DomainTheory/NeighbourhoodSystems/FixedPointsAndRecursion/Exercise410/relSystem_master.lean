/-ai
The master neighbourhood of the relativized system below an element a is the master neighbourhood of the original system.

This is the defining equation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

@[simp] theorem relSystem_master (a : V.Element) : (relSystem a).master = V.master := rfl

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
