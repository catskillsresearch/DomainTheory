module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLevelSetNonempty

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem myLevelSetNonempty_le_one (k m : ℕ) : myLevelSetNonempty k m ≤ 1 :=
  bExistsFn_le_one _ _ _

end DomainTheory.NeighbourhoodSystems
