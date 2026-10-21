/-ai
The maximum second component of a list of rational pairs is the left fold of the maximum of the second components, seeded at zero.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `max_i pᵢ.2` over a presenting list, folded with seed `0`. -/
def listMaxSnd (L : List (ℚ × ℚ)) : ℚ := L.foldl (fun acc p => max acc p.2) 0

end DomainTheory.NeighbourhoodSystems
