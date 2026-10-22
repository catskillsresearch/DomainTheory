module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2MidCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.decodeRat_splitU2MidCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2_min_lt_max

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem splitU2_mid_lt_max (n : ℕ) :
    decodeRat (splitU2MidCode n) < listMaxSnd (decodeQPairList (canonCode n)) := by
  rw [decodeRat_splitU2MidCode]; exact add_div_two_lt_right.mpr (splitU2_min_lt_max n)

end DomainTheory.NeighbourhoodSystems
