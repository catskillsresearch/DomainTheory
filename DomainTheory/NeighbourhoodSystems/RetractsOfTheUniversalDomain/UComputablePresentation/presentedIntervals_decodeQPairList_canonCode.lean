module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.qpClip
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.presentedIntervals_map_qpClip
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.presentedIntervals_filter_qpPos
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonList_eq_of_filter_eq_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonList_eq_of_filter_eq_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.presentedIntervals_decodeQPairList_canonListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.presentedIntervals_eq_empty_iff_of_forall_lt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeQPairList_canonListCode_eq_nil_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.masterPairCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_masterPairCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeQPairList_masterCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`canonCode` realizes `canonList` at the `presentedIntervals` level.** -/
theorem presentedIntervals_decodeQPairList_canonCode (c : ℕ) :
    presentedIntervals (decodeQPairList (canonCode c))
      = presentedIntervals (canonList (decodeQPairList c)) := by
  have hfilterPos : ∀ p ∈ ((decodeQPairList c).map qpClip).filter (fun p => decide (p.1 < p.2)),
      p.1 < p.2 := fun p hp => by simpa using (List.mem_filter.mp hp).2
  by_cases hne : (presentedIntervals (decodeQPairList c) ∩ Set.Ico (0 : ℚ) 1).Nonempty
  · have hnc : (presentedIntervals (decodeQPairList (canonListCode c))).Nonempty := by
      rwa [presentedIntervals_decodeQPairList_canonListCode]
    have hcne : canonListCode c ≠ 0 := by
      intro h
      apply hnc.ne_empty
      unfold decodeQPairList
      rw [h, decodeList_zero, List.map_nil]
      exact presentedIntervals_nil
    have hzero : isZero (canonListCode c) = 0 := by
      by_contra hz
      have h1 := isZero_le_one (canonListCode c)
      exact hcne ((isZero_eq_one_iff _).mp (by omega))
    have hcc : canonCode c = canonListCode c := by unfold canonCode; rw [hzero, selectFn_zero]
    have hL'ne : ((decodeQPairList c).map qpClip).filter (fun p => decide (p.1 < p.2)) ≠ [] := by
      rw [Ne, ← presentedIntervals_eq_empty_iff_of_forall_lt hfilterPos,
        presentedIntervals_filter_qpPos, presentedIntervals_map_qpClip]
      exact hne.ne_empty
    rcases hL : ((decodeQPairList c).map qpClip).filter (fun p => decide (p.1 < p.2)) with _ | ⟨a, l⟩
    · exact absurd hL hL'ne
    · rw [hcc, presentedIntervals_decodeQPairList_canonListCode, canonList_eq_of_filter_eq_cons hL,
        ← hL, presentedIntervals_filter_qpPos, presentedIntervals_map_qpClip]
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hLnil : decodeQPairList (canonListCode c) = [] := by
      rw [decodeQPairList_canonListCode_eq_nil_iff, presentedIntervals_decodeQPairList_canonListCode,
        hne]
    have hczero : canonListCode c = 0 := by
      have h' := hLnil
      unfold decodeQPairList at h'
      rwa [List.map_eq_nil_iff, decodeList_eq_nil_iff] at h'
    have hzero : isZero (canonListCode c) = 1 := by rw [hczero]; exact (isZero_eq_one_iff 0).mpr rfl
    have hcc : canonCode c = Nat.pair masterPairCode 0 + 1 := by
      unfold canonCode; rw [hzero, selectFn_one]
    have hLnil' : ((decodeQPairList c).map qpClip).filter (fun p => decide (p.1 < p.2)) = [] := by
      rw [← presentedIntervals_eq_empty_iff_of_forall_lt hfilterPos, presentedIntervals_filter_qpPos,
        presentedIntervals_map_qpClip]
      exact hne
    rw [hcc, decodeQPairList_masterCode, canonList_eq_of_filter_eq_nil hLnil']

end DomainTheory.NeighbourhoodSystems
