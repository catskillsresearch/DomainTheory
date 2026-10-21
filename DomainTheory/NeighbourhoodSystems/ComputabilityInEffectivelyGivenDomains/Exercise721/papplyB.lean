/-ai
The product form of the evaluation lift is the two-argument approximable map, from the product of the power domain of the function space with the power domain of the source into the power domain of the target, obtained by packaging the evaluation lift.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise721.papplyEval
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise721.papplyEval_rel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

/-- **Exercise 7.21 — the combinator as a map out of the product `ℙ(D→E) × ℙD → ℙE`.** -/
def papplyB (V : NeighborhoodSystem α) (W : NeighborhoodSystem β) :
    ApproximableMap (prod (funSpace V W).PowerDomain V.PowerDomain) W.PowerDomain :=
  ofMap₂ (papplyEval V W)

end DomainTheory.NeighbourhoodSystems
