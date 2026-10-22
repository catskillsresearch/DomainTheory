/-ai
matchesB decides, by recursion on the expression, whether a word belongs to the denoted language. The universal expression accepts every word, a singleton accepts the word equal to its list, a concatenation accepts a word when some cut has its prefix accepted by the first factor and its suffix accepted by the second, and an intersection accepts a word when both factors accept it.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.SExpr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.BasicInst7
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_sigma
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_single
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_cap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

/-- The **`Bool` matcher** for `S`-terms: a structurally-recursive decision of word membership. The
concatenation case tries every cut point `i ∈ {0,…,|w|}`; the intersection case is the conjunction. -/
def matchesB : SExpr → List Bool → Bool
  | .sigma, _ => true
  | .single σ, w => decide (w = σ)
  | .cat a b, w => (List.range (w.length + 1)).any (fun i => matchesB a (w.take i) && matchesB b (w.drop i))
  | .cap a b, w => matchesB a w && matchesB b w

end Exercise722

end DomainTheory.NeighbourhoodSystems
