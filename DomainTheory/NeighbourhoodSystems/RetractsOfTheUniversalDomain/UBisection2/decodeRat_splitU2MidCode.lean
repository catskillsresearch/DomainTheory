/-ai
Decoding the presentation-independent midpoint code is half the sum of the minimum first component and the maximum second component of the decoded canonical list.

Unfold the midpoint code and rewrite by decoding of the rational midpoint, the unpairing of a pair, and the two decoding lemmas for the minimum and maximum codes.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.decodeRat_listMinFstCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.decodeRat_listMaxSndCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2MidCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem decodeRat_splitU2MidCode (n : ℕ) :
    decodeRat (splitU2MidCode n) =
      (listMinFst (decodeQPairList (canonCode n)) + listMaxSnd (decodeQPairList (canonCode n)))
        / 2 := by
  unfold splitU2MidCode
  rw [decodeRat_ratMidCode', unpair_pair_fst, unpair_pair_snd, decodeRat_listMinFstCode,
    decodeRat_listMaxSndCode]

end DomainTheory.NeighbourhoodSystems
