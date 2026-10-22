module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.foldl_minFst_le

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem listMinFst_le {L : List (ℚ × ℚ)} {p : ℚ × ℚ} (hp : p ∈ L) : listMinFst L ≤ p.1 :=
  foldl_minFst_le L 1 p hp

end DomainTheory.NeighbourhoodSystems
