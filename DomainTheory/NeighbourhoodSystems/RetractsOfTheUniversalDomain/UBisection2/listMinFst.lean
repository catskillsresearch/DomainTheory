/-ai
The minimum first component of a list of rational pairs is the left fold of the minimum of the first components, seeded at one.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `min_i pᵢ.1` over a presenting list, folded with seed `1` (safe: every genuine pair has
`p.1 < 1` once bounded, `forall_bounds_decodeQPairList_canonCode`). -/
def listMinFst (L : List (ℚ × ℚ)) : ℚ := L.foldl (fun acc p => min acc p.1) 1

end DomainTheory.NeighbourhoodSystems
