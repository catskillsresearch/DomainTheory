/-ai
The joint evaluator of an endomap c of the universal domain sends a packaged triple consisting of two maps and a point to c applied after the second map applied after the first map. It is c composed with evaluation of the first component of the inner pair against the evaluation of the outer first component at the second component of the inner pair.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.RDom

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.NeighborhoodSystemu2eIsEffectivelyGivenu2etoS
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- `R(ψ, φ, x) := c(φ(ψ(x)))`, purely as a composite of `evalMap`, `proj`s and `paired` — jointly
continuous in `(ψ, φ, x)` since `evalMap` is. -/
noncomputable def RMap (c : ApproximableMap U U) : ApproximableMap RDom U :=
  c.comp ((evalMap U U).comp
    (paired
      ((proj₀ (funSpace U U) U).comp (proj₁ (funSpace U U) (prod (funSpace U U) U)))
      ((evalMap U U).comp
        (paired (proj₀ (funSpace U U) (prod (funSpace U U) U))
          ((proj₁ (funSpace U U) U).comp (proj₁ (funSpace U U) (prod (funSpace U U) U)))))))

end DomainTheory.NeighbourhoodSystems
