/-ai
The bitmask of a finite set of positions is the sum of the corresponding powers of two.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.GeneratedBy

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- Build a natural number with a prescribed (finite) set of bits set — the "witness" constructor
used both for `generator`'s `levelSet` realization and for the complement/independence proofs
below. -/
def bitmaskOf (s : Finset ℕ) : ℕ := ∑ j ∈ s, 2 ^ j

end DomainTheory.NeighbourhoodSystems
