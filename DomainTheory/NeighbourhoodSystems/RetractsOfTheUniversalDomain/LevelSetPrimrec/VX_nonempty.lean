/-ai
Every value of the enumeration of V is nonempty.

It is the nonemptiness of the level set presented by a canonicalized code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_canonIdx_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VX

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem VX_nonempty (c : ℕ) : (VX c).Nonempty := levelSet_canonIdx_nonempty c

end DomainTheory.NeighbourhoodSystems
