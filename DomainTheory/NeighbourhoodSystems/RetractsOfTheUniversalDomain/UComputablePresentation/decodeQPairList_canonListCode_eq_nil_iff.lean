/-ai
The rational-pair list decoded from a canonical list code is empty if and only if it presents the empty set. Every pair in that list is already nondegenerate.

This is the reverse of the emptiness criterion for a list of nondegenerate pairs. Each decoded pair is the clip of a source pair whose clip is nondegenerate, so the strict inequality holds.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.mem_decodeQPairList_canonListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.presentedIntervals_eq_empty_iff_of_forall_lt

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Every element of `decodeQPairList (canonListCode c)` is already non-degenerate (this is
`canonFilterStep`'s whole point), so — unlike an arbitrary list — this particular list is empty
iff its `presentedIntervals` is empty. -/
theorem decodeQPairList_canonListCode_eq_nil_iff (c : ℕ) :
    decodeQPairList (canonListCode c) = [] ↔
      presentedIntervals (decodeQPairList (canonListCode c)) = ∅ :=
  (presentedIntervals_eq_empty_iff_of_forall_lt (fun p hp => by
    obtain ⟨p0, hp0, hcond, rfl⟩ := (mem_decodeQPairList_canonListCode c p).mp hp
    exact hcond)).symm

end DomainTheory.NeighbourhoodSystems
