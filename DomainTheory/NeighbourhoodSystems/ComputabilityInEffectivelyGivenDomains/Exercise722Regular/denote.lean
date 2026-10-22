module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.SExpr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.BasicInst7

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

/-- The language denoted by an `S`-term. -/
def denote : SExpr → Set (List Bool)
  | .sigma => Set.univ
  | .single σ => {σ}
  | .cat a b => concat (denote a) (denote b)
  | .cap a b => denote a ∩ denote b

end Exercise722

end DomainTheory.NeighbourhoodSystems
