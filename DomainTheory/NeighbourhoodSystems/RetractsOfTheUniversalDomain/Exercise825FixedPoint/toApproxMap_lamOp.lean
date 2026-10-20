module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Pow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Closing
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.toElementMap_RMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap















/-- **`lamOp c` recovers `expMap (-) c = lamComb (-) c` at every `a`.** The heart of the
continuity argument: unwinding both curry layers (`curryC_toApproxMap`, `toElementMap_curry_apply`
twice) and `RMap`'s value formula (`toElementMap_RMap`) against `expMap`'s own value formula
(`toApproxMap_toElementMap_expMap`) shows both sides send `φ` to (the element representing)
`x ↦ c(φ(a(x)))`. -/
theorem toApproxMap_lamOp (c a : ApproximableMap U U) :
    toApproxMap ((lamOp c).toElementMap (toFilter a)) = expMap a c := by
  apply ApproximableMap.ext_of_toElementMap
  intro φ
  apply (funSpaceEquiv U U).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply]
  apply ApproximableMap.ext_of_toElementMap
  intro x
  show (toApproxMap ((toApproxMap ((lamOp c).toElementMap (toFilter a))).toElementMap φ)).toElementMap x
    = (toApproxMap ((expMap a c).toElementMap φ)).toElementMap x
  rw [lamOp, toElementMap_comp, curryC_toApproxMap, toElementMap_curry_apply, curryOnceC,
    toElementMap_curry_apply, toElementMap_RMap, Sub8_6.toApproxMap_toFilter,
    toApproxMap_toElementMap_expMap, toElementMap_comp, toElementMap_comp]

end DomainTheory.NeighbourhoodSystems
