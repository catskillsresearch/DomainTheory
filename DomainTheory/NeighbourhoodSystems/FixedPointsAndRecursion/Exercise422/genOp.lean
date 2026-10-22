module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise422

open DomainTheory.NeighbourhoodSystems DomainTheory.NeighbourhoodSystems.Exercise414

variable {M : Type*} (zero : M) (succ : M → M)

/-- Scott's operator `g(x) = {0} ∪ x⁺` on `P(N*)`, whose least fixed point is the smallest subset
containing `0` and closed under the successor. -/
def genOp (x : Set M) : Set M := {zero} ∪ succ '' x

end DomainTheory.NeighbourhoodSystems.Exercise422
