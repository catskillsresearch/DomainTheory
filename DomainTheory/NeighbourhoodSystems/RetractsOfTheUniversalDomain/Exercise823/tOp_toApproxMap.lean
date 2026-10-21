/-ai
The induced operator, applied to the map read from an element of the function space, is the map read from the image of that element.

Unfold the operator and cancel the filter of a read map against the element it came from.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise816
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6

namespace Exercise823

variable {α : Type} {E : NeighborhoodSystem α}


theorem tOp_toApproxMap (t : ApproximableMap (funSpace E E) (funSpace E E))
    (φ : (funSpace E E).Element) : tOp t (toApproxMap φ) = toApproxMap (t.toElementMap φ) := by
  unfold tOp
  rw [toFilter_toApproxMap]

end Exercise823
end DomainTheory.NeighbourhoodSystems
