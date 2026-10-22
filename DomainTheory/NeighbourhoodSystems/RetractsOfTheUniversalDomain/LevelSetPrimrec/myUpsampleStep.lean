module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myModPow2

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- One computable upsampling step: re-express a level-`k` mask at level `k + 1` by duplicating its
low `2^k` bits into a second copy shifted up by `2^k` positions. -/
def myUpsampleStep (k m : ℕ) : ℕ :=
  2 ^ (2 ^ k) * myModPow2 m (2 ^ k) + myModPow2 m (2 ^ k)

end DomainTheory.NeighbourhoodSystems
