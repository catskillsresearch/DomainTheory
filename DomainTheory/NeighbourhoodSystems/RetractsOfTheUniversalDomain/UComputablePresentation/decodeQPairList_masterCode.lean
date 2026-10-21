/-ai
The singleton list code of the master pair decodes to the singleton list of the pair zero and one, the presenting list of the master neighbourhood of U.

Unfold the pair-list decoding, rewrite the successor and its zero tail, and simplify by the decoding of the master pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.masterPairCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_masterPairCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The singleton list-code `[masterPairCode]` decodes to the singleton presenting list of
`U.master`. -/
theorem decodeQPairList_masterCode :
    decodeQPairList (Nat.pair masterPairCode 0 + 1) = [((0 : ℚ), (1 : ℚ))] := by
  unfold decodeQPairList
  rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero]
  simp [decodeRatPair_masterPairCode]

end DomainTheory.NeighbourhoodSystems
