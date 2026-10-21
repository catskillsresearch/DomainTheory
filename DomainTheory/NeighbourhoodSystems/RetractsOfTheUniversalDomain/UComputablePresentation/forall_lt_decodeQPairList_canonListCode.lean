/-ai
Every pair decoded from a canonical list code has left endpoint strictly less than its right endpoint.

Membership supplies a source pair whose clip is nondegenerate and equals the given pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem




























/-- Every pair in `decodeQPairList (canonListCode c)` is already non-degenerate (this is
`canonFilterStep`'s whole point). -/
theorem forall_lt_decodeQPairList_canonListCode (c : ℕ) :
    ∀ p ∈ decodeQPairList (canonListCode c), p.1 < p.2 := fun p hp => by
  obtain ⟨p0, -, hcond, rfl⟩ := (mem_decodeQPairList_canonListCode c p).mp hp
  exact hcond

end DomainTheory.NeighbourhoodSystems
