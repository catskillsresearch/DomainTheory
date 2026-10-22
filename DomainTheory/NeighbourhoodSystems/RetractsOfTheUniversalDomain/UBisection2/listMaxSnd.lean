module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `max_i pᵢ.2` over a presenting list, folded with seed `0`. -/
def listMaxSnd (L : List (ℚ × ℚ)) : ℚ := L.foldl (fun acc p => max acc p.2) 0

end DomainTheory.NeighbourhoodSystems
