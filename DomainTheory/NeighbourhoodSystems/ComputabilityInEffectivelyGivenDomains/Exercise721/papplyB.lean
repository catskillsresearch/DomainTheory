module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise721.papplyEval
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise721.papplyEval_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

/-- **Exercise 7.21 — the combinator as a map out of the product `ℙ(D→E) × ℙD → ℙE`.** -/
def papplyB (V : NeighborhoodSystem α) (W : NeighborhoodSystem β) :
    ApproximableMap (prod (funSpace V W).PowerDomain V.PowerDomain) W.PowerDomain :=
  ofMap₂ (papplyEval V W)

end DomainTheory.NeighbourhoodSystems
