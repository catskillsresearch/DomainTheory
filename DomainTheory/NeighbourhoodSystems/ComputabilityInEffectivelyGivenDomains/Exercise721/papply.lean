module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise721.papplyEval_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise721.papplyB

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

/-- **Exercise 7.21 — the headline combinator `papply : ℙ(D→E) → (ℙD → ℙE)`.** Currying `papplyB`
(Theorem 3.12) gives the combinator of *exactly* the type Scott asks for. -/
def papply (V : NeighborhoodSystem α) (W : NeighborhoodSystem β) :
    ApproximableMap (funSpace V W).PowerDomain (funSpace V.PowerDomain W.PowerDomain) :=
  curry (papplyB V W)

end DomainTheory.NeighbourhoodSystems
