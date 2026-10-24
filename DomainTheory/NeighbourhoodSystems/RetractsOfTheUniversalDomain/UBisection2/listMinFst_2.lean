module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.bisection

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace listMinFst

open Domain.Recursive NeighborhoodSystem


theorem le_one (L : List (ℚ × ℚ)) : listMinFst L ≤ 1 := foldl.minFst_le_seed L 1

end listMinFst
end DomainTheory.NeighbourhoodSystems
