module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSetNonemptyBody

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`myLevelSetNonempty k m ∈ {0,1}`** decides `(levelSet k m).Nonempty`
(`myLevelSetNonempty_eq_one_iff`). -/
def myLevelSetNonempty (k m : ℕ) : ℕ := bExistsFn levelSetNonemptyBody m (2 ^ k)

end DomainTheory.NeighbourhoodSystems
