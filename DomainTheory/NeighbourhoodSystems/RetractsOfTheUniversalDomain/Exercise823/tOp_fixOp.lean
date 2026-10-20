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










/-- **`‖t‖` is a genuine (not merely approximate) fixed point of `t`.** -/
theorem tOp_fixOp (t : ApproximableMap (funSpace E E) (funSpace E E)) :
    tOp t (fixOp t) = fixOp t := by
  show toApproxMap (t.toElementMap (toFilter (toApproxMap t.fixElement))) = toApproxMap t.fixElement
  rw [toFilter_toApproxMap, toElementMap_fixElement]

end Exercise823
end DomainTheory.NeighbourhoodSystems
