module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.decodeRat_listMinFstCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.decodeRat_listMaxSndCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2MidCode

@[expose] public section

set_option linter.unusedSectionVars false

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
