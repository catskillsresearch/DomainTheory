/-ai
Decoding the singleton list code of a pair code v yields the one-element list whose entry is the decoded rational pair of v.

Unfold decoding of the list, rewrite the successor code by the list-decoding equation and the unpair-pair identities, and use that the tail code decodes to the empty list.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem










theorem decodeQPairList_singletonCode (v : ℕ) :
    decodeQPairList (Nat.pair v 0 + 1) = [decodeRatPair v] := by
  unfold decodeQPairList
  rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero]
  rfl

end DomainTheory.NeighbourhoodSystems
