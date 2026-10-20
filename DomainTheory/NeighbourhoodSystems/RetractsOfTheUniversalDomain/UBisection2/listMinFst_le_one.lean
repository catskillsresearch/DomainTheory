module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem













theorem listMinFst_le_one (L : List (ℚ × ℚ)) : listMinFst L ≤ 1 := foldl_minFst_le_seed L 1

end DomainTheory.NeighbourhoodSystems
