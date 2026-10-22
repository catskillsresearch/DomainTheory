module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.qpClip
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonFilterStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeQPairList_canonFilterStep

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem mem_decodeQPairList_canonFilterStep (e : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (canonFilterStep e) ↔
      (qpClip (decodeRatPair e)).1 < (qpClip (decodeRatPair e)).2 ∧ p = qpClip (decodeRatPair e) := by
  rw [decodeQPairList_canonFilterStep]
  by_cases h : (qpClip (decodeRatPair e)).1 < (qpClip (decodeRatPair e)).2
  · simp [h]
  · simp [h]

end DomainTheory.NeighbourhoodSystems
