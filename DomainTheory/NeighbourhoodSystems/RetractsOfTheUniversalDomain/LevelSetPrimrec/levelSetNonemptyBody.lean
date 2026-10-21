/-ai
The body of the bounded existential for level-set nonemptiness sends a code of a bit
index and a mask to the test of that bit of the mask.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myTestBit

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The `bExistsFn` body `pair ℓ m ↦ myTestBit m ℓ`. -/
def levelSetNonemptyBody (t : ℕ) : ℕ := myTestBit t.unpair.2 t.unpair.1

end DomainTheory.NeighbourhoodSystems
