/-ai
Decoding a clipped pair code yields the clip of the decoded pair.

Unfold the clip code, the clip, and the pair decoding. After unpacking the pair, rewrite the rational maximum and minimum and the codes of zero and one.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.qpClip
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.qpClipCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem decodeRatPair_qpClipCode (e : ℕ) :
    decodeRatPair (qpClipCode e) = qpClip (decodeRatPair e) := by
  unfold qpClipCode qpClip decodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [decodeRat_ratMaxCode, decodeRat_ratMinCode, decodeRat_zeroCode, decodeRat_oneCode]

end DomainTheory.NeighbourhoodSystems
