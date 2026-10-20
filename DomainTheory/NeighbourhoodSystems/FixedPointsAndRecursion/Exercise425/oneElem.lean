module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.mem_tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.memC1_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- The total element `1ⁿ = ↑{n}` (the finite string of exactly `n` ones). -/
def oneElem (n : ℕ) : C1.Element := C1.principal (memC1_singleton n)

end DomainTheory.NeighbourhoodSystems.Exercise425
