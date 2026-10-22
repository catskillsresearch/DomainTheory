module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


theorem zero_le_listMaxSnd (L : List (ℚ × ℚ)) : 0 ≤ listMaxSnd L := foldl_maxSnd_seed_le L 0

end DomainTheory.NeighbourhoodSystems
