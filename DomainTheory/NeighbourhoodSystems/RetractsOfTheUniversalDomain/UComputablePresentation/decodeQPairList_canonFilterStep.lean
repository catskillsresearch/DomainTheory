/-ai
Decoding the filter step as rational pairs yields the singleton of the clipped decoded pair when that pair is nondegenerate, and the empty list otherwise.

Unfold the pair-list decoding, rewrite by the list decoding of the filter step, and simplify both branches by the decoding of the clipped pair code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.qpClip
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_qpClipCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonFilterStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeList_canonFilterStep

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem decodeQPairList_canonFilterStep (e : ℕ) :
    decodeQPairList (canonFilterStep e)
      = if (qpClip (decodeRatPair e)).1 < (qpClip (decodeRatPair e)).2
        then [qpClip (decodeRatPair e)] else [] := by
  unfold decodeQPairList
  rw [decodeList_canonFilterStep]
  split <;> simp [decodeRatPair_qpClipCode]

end DomainTheory.NeighbourhoodSystems
