/-ai
The second component of any pair in a list is at most the maximum second component of the list.

Apply the corresponding inequality for the left fold at seed zero.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.foldl_maxSnd_ge

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem listMaxSnd_ge {L : List (ℚ × ℚ)} {p : ℚ × ℚ} (hp : p ∈ L) : p.2 ≤ listMaxSnd L :=
  foldl_maxSnd_ge L 0 p hp

end DomainTheory.NeighbourhoodSystems
