module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.nats

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise422

open DomainTheory.NeighbourhoodSystems DomainTheory.NeighbourhoodSystems.Exercise414

variable {M : Type*} (zero : M) (succ : M → M)

/-- The subtype `N = {m // m ∈ nats}` carrying the carved-out Peano structure. -/
abbrev Nat' : Type _ := {m : M // m ∈ nats zero succ}

end DomainTheory.NeighbourhoodSystems.Exercise422
