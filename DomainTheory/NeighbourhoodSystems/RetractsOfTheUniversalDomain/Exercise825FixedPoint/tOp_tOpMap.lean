/-ai
The abstract operator of the continuous operator, applied to any endomap, equals the arrow combinator of that endomap with the given endomap.

Unfold the abstract operator as the approximable map of the element action on the filter of the endomap. Rewrite by the definition of the continuous operator, the element action of a composite, the approximable map of the exponential, the recovery of the exponential by the second curry, and the equality of the exponential with the lambda combinator. The resulting goal is definitional.
ai-/
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.toApproxMap_lamOp

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

















/-- **`tOp (tOpMap c) a = arrowComb a c`**, for every `a`: `t` really does implement
`a ↦ arrowComb a c`, continuously. -/
theorem tOp_tOpMap (c a : ApproximableMap U U) :
    Exercise823.tOp (tOpMap c) a = arrowComb a c := by
  show toApproxMap ((tOpMap c).toElementMap (toFilter a)) = arrowComb a c
  rw [tOpMap, toElementMap_comp, toApproxMap_toElementMap_expMap, toApproxMap_lamOp,
    expMap_eq_lamComb]
  rfl

end DomainTheory.NeighbourhoodSystems
