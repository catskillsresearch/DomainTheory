/-ai
denote sends an expression to a language of words. The universal expression denotes every word, a singleton expression denotes that one word, a concatenation denotes the concatenation of the two languages, and an intersection denotes the intersection of the two languages.
ai-/
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
