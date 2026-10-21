/-ai
The joint upsampling step sends a code of a level and a mask to the code of the
successor level and the one-step upsampling of that mask.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleStep

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Joint (level, mask) iteration state for `myUpsample`: `pair level mask`. -/
def myUpsampleJointStep (s : ℕ) : ℕ :=
  Nat.pair (s.unpair.1 + 1) (myUpsampleStep s.unpair.1 s.unpair.2)

end DomainTheory.NeighbourhoodSystems
