module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise409.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise409.bigPsi_apply
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise409.toApproxMap_toFilter_fixMap

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixMap_toElementMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.toElementMap_fixElement
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*}


/-- **Exercise 4.9 (Scott 1981, PRG-19).** `fix` is a *fixed point* of `Ψ`: `Ψ(fix) = fix`. -/
theorem bigPsi_fix (V : NeighborhoodSystem α) :
    (bigPsi V).toElementMap (toFilter (fixMap V)) = toFilter (fixMap V) := by
  apply (funSpaceEquiv (funSpace V V) V).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply]
  apply ext_of_toElementMap
  intro f
  rw [bigPsi_apply, toApproxMap_toFilter_fixMap, fixMap_toElementMap, toElementMap_fixElement]

end DomainTheory.NeighbourhoodSystems
