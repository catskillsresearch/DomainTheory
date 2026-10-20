module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.qpClip
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.qpClipCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_qpClipCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonFilterStep

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem decodeList_canonFilterStep (e : ℕ) :
    decodeList (canonFilterStep e)
      = if (qpClip (decodeRatPair e)).1 < (qpClip (decodeRatPair e)).2
        then [qpClipCode e] else [] := by
  unfold canonFilterStep
  by_cases h : qpNonemptyBop (qpClipCode e) = 1
  · rw [h, selectFn_one]
    have h' : (decodeRatPair (qpClipCode e)).1 < (decodeRatPair (qpClipCode e)).2 :=
      (qpNonemptyBop_eq_one_iff (qpClipCode e)).mp h
    rw [decodeRatPair_qpClipCode] at h'
    simp [h', decodeList_succ, decodeList_zero]
  · have h0 : qpNonemptyBop (qpClipCode e) = 0 := by
      have := ratLtCode_le_one (Nat.pair (qpClipCode e).unpair.1 (qpClipCode e).unpair.2)
      unfold qpNonemptyBop at h ⊢; omega
    rw [h0, selectFn_zero]
    have hnot : ¬ (decodeRatPair (qpClipCode e)).1 < (decodeRatPair (qpClipCode e)).2 := by
      rw [← qpNonemptyBop_eq_one_iff]; omega
    rw [decodeRatPair_qpClipCode] at hnot
    simp [hnot, decodeList_zero]

end DomainTheory.NeighbourhoodSystems
