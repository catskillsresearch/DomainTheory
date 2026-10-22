/-ai
The finite join of a family of n elements, as an element of the power domain, is the empty join when n is zero and the successor join otherwise.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711.PDfinJoinZero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711.PDfinJoinSucc

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Definition 7.11.** The finite-element join `{x₀,…,x_{n-1}}` in `|ℙ𝒟|`. The empty
family yields `⊥`; otherwise use Scott's union-of-down-sets condition. -/
def PDfinJoin (n : ℕ) (xs : Fin n → V.Element) : V.PowerDomain.Element :=
  match n with
  | 0 => V.PDfinJoinZero
  | _m + 1 => V.PDfinJoinSucc xs

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
