module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.mem_tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.memC1_tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- The partial element `1ⁿ⊥ = ↑(tail n)` ("at least `n` ones"). -/
def oneBot (n : ℕ) : C1.Element := C1.principal (memC1_tail n)

end DomainTheory.NeighbourhoodSystems.Exercise425
