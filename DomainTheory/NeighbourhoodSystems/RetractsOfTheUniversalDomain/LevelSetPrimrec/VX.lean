/-ai
The enumeration of V sends a code to the level set of the level and mask obtained by
canonicalizing that code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.canonIdx

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`V`'s enumeration**: canonicalize the `(level, mask)` pair coded by `n`. -/
def VX (c : ℕ) : Set ℕ := levelSet (canonIdx c).unpair.1 (canonIdx c).unpair.2

end DomainTheory.NeighbourhoodSystems
