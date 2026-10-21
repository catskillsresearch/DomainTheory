/-ai
The intervals presented by the list decoded from a canonical list code equal the original presented intervals cut by the half-open unit interval.

Rewrite the cut as the intervals presented by the clipped list filtered to nondegenerate pairs. The two lists have the same members: membership in the decoded canonical list code is being the nondegenerate clip of an original pair, which is membership in that filtered clipped list.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.qpClip
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.presentedIntervals_map_qpClip
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.presentedIntervals_filter_qpPos
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.mem_decodeQPairList_canonListCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`canonListCode` realizes the clip-and-filter pass at the `presentedIntervals` level.** -/
theorem presentedIntervals_decodeQPairList_canonListCode (c : ℕ) :
    presentedIntervals (decodeQPairList (canonListCode c))
      = presentedIntervals (decodeQPairList c) ∩ Set.Ico (0 : ℚ) 1 := by
  rw [← presentedIntervals_map_qpClip, ← presentedIntervals_filter_qpPos ((decodeQPairList c).map qpClip)]
  apply presentedIntervals_congr
  intro p
  rw [mem_decodeQPairList_canonListCode, List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨p0, hp0, hcond, rfl⟩
    exact ⟨⟨p0, hp0, rfl⟩, decide_eq_true_eq.mpr hcond⟩
  · rintro ⟨⟨p0, hp0, hp⟩, hcond⟩
    rw [decide_eq_true_eq] at hcond
    exact ⟨p0, hp0, hp ▸ hcond, hp.symm⟩

end DomainTheory.NeighbourhoodSystems
